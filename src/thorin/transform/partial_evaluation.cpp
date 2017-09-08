#include "thorin/primop.h"
#include "thorin/world.h"
#include "thorin/analyses/cfg.h"
#include "thorin/analyses/free_defs.h"
#include "thorin/util/hash.h"
#include "thorin/util/log.h"

#include <map>
#include <stack>

namespace thorin {

class CondEval {
public:
    CondEval(Continuation* callee, Defs args, ContinuationMap<bool>& top_level)
        : callee_(callee)
        , args_(args)
        , top_level_(top_level)
    {
        assert(callee->pe_profile().empty() || callee->pe_profile().size() == args.size());
        assert(callee->num_params() == args.size());

        for (size_t i = 0, e = args.size(); i != e; ++i)
            old2new_[callee->param(i)] = args[i];
    }

    World& world() { return callee_->world(); }
    const Def* instantiate(const Def* odef) {
        if (auto ndef = find(old2new_, odef))
            return ndef;

        if (auto oprimop = odef->isa<PrimOp>()) {
            Array<const Def*> new_ops(oprimop->num_ops());
            for (size_t i = 0; i != oprimop->num_ops(); ++i)
                new_ops[i] = instantiate(odef->op(i));

            auto nprimop = oprimop->rebuild(new_ops);
            return old2new_[oprimop] = nprimop;
        }

        return old2new_[odef] = odef;
    }

    bool eval(size_t i) {
        // the only higher order parameter that is allowed is a single 1st-order parameter of a top-level continuation
        // all other parameters need specialization (lower2cff)
#if 0
        auto order = callee_->param(i)->order();
        if (order >= 2 || (order == 1 && (!callee_->is_returning() || !is_top_level(callee_)))) {
            DLOG("bad param({}) {} of continuation {}", i, callee_->param(i), callee_);
            return true;
        }
#endif

        return is_one(instantiate(pe_profile(i))) ? true : false;
    }

    const Def* pe_profile(size_t i) {
        return callee_->pe_profile().empty() ? world().literal_bool(false, {}) : callee_->pe_profile(i);
    }

    bool is_top_level(Continuation* continuation) {
        auto p = top_level_.emplace(continuation, true);
        if (p.second && has_free_vars(callee_))
            return p.first->second = false;

        return p.first->second;
    }

private:
    Continuation* callee_;
    Defs args_;
    Def2Def old2new_;
    ContinuationMap<bool> top_level_;
};

class Closure : public Def {
public:
    Closure(Continuation* continuation)
        : Def(Node_Closure, continuation->type(), 1, Debug{})
    {
        set_op(0, continuation);
    }

    Continuation* continuation() const { return op(0)->as_continuation(); }
};

class PartialEvaluator {
public:
    struct Context {
        Context(const Scope& scope, Defs args)
            : scope(scope)
            , args(args)
            , old2new(std::make_unique<Def2Def>(scope.defs().capacity()))
        {}

        Continuation* old_entry() const { return scope.entry(); }

        const Scope& scope;
        Defs args;
        std::unique_ptr<Def2Def> old2new;
        Continuation* new_entry;
    };

    PartialEvaluator(World& world)
        : world_(world)
    {}

    World& world() { return world_; }
    const Def* old2new(const Def* old_def) {
        if (auto new_def = find(*stack_.back().old2new, old_def))
            return new_def;
        return nullptr;
    }
    void old2new(const Def* old_def, const Def* new_def) {
        stack_.back().old2new->emplace(old_def, new_def);
    }

    bool within(const Def* def) {
        return stack_.back().scope.contains(def);
        //for (size_t i = stack_.size(); i-- != 0;) {
            //if (stack_[i].scope.contains(def))
                //return true;
        //}
        //return false;
    }

    void specialize_top_level(const Scope& scope);
    Continuation* specialize_scope(const Scope&, Defs args);
    Continuation* specialize_head(Continuation* old_continuation);
    Call specialize_call(Call);
    void specialize_body(Continuation* old_continuation, Continuation* new_continuation);
    const Def* specialize(const Def* old_def);

private:
    World& world_;
    HashMap<Call, Continuation*> cache_;
    std::map<Continuation*, Scope, GIDLt<Continuation>> continuation2scope_;
    std::vector<Context> stack_;
    ContinuationMap<bool> top_level_;
};

void PartialEvaluator::specialize_top_level(const Scope& scope) {
    //outf("specialize_top_level: {}\n", scope.entry());
    auto entry = scope.entry();
    stack_.emplace_back(scope, Array<const Def*>(entry->num_params()));
    stack_.back().new_entry = entry;

    // map value params
    old2new(entry, entry);
    for (auto param : entry->params())
        old2new(param, param);

    auto call = specialize_call({entry->ops()});
    entry->jump(call.callee(), call.args(), entry->jump_debug());
    stack_.pop_back();
}

Continuation* PartialEvaluator::specialize_scope(const Scope& scope, Defs args) {
    //outf("specialize_scope: {}\n", scope.entry());
    auto old_entry = scope.entry();
    stack_.emplace_back(scope, args);

    std::vector<const Type*> param_types;
    for (size_t i = 0, e = old_entry->num_params(); i != e; ++i) {
        if (args[i] == nullptr)
            param_types.emplace_back(old_entry->param(i)->type());
    }

    auto fn_type = world().fn_type(param_types);
    auto new_entry = world().continuation(fn_type, old_entry->debug_history());
    stack_.back().new_entry = new_entry;

    // map value params
    old2new(old_entry, old_entry);
    for (size_t i = 0, j = 0, e = old_entry->num_params(); i != e; ++i) {
        auto old_param = old_entry->param(i);
        if (auto new_def = args[i])
            old2new(old_param, new_def);
        else {
            auto new_param = new_entry->param(j++);
            old2new(old_param, new_param);
            new_param->debug().set(old_param->name());
        }
    }

    // specialize pe_profile
    if (!old_entry->pe_profile().empty()) {
        Array<const Def*> new_pe_profile(new_entry->num_params());
        size_t j = 0;
        for (size_t i = 0, e = old_entry->num_params(); i != e; ++i) {
            if (args[i] == nullptr)
                new_pe_profile[j++] = specialize(old_entry->pe_profile(i));
        }

        for (size_t e = new_entry->num_params(); j != e; ++j)
            new_pe_profile[j] = world().literal_bool(false, Debug{});

        new_entry->set_pe_profile(new_pe_profile);
    }

    auto call = specialize_call({old_entry->ops()});
    new_entry->jump(call.callee(), call.args(), old_entry->jump_debug());
    stack_.pop_back();

    return new_entry;
}

const Def* PartialEvaluator::specialize(const Def* old_def) {
    if (auto new_def = old2new(old_def))
        return new_def;

    if (!within(old_def))
        return old_def;

    if (auto old_continuation = old_def->isa_continuation()) {
        auto new_continuation = specialize_head(old_continuation);
        specialize_body(old_continuation, new_continuation);
        return new_continuation;
    }

    if (auto param = old_def->isa<Param>()) {
        assert(within(param->continuation()));
        specialize(param->continuation());
        auto new_def = old2new(param);
        assert(new_def != nullptr);
        return new_def;
    }

    auto old_primop = old_def->as<PrimOp>();
    Array<const Def*> new_ops(old_primop->num_ops());
    for (size_t i = 0, e = old_primop->num_ops(); i != e; ++i)
        new_ops[i] = specialize(old_primop->op(i));

    auto new_primop = old_primop->rebuild(new_ops, old_primop->type());
    old2new(old_primop, new_primop);
    return new_primop;
}

Continuation* PartialEvaluator::specialize_head(Continuation* old_continuation) {
    assert(old2new(old_continuation) == nullptr);
    assert(!old_continuation->empty());

    auto new_continuation = old_continuation->stub();
    old2new(old_continuation, new_continuation);

    for (size_t i = 0, e = old_continuation->num_params(); i != e; ++i)
        old2new(old_continuation->param(i), new_continuation->param(i));

    return new_continuation;
}

Call PartialEvaluator::specialize_call(Call call) {
    //outf("specialize_call to: {}\n", call.callee());
    if (call.callee() == world().branch()) {        // fold branch if possible
        if (auto lit = specialize(call.arg(0))->isa<PrimLit>())
            return Call(Defs{specialize(lit->value().get_bool() ? call.arg(1) : call.arg(2))});
    }

    Array<const Def*> new_ops(call.num_ops());
    for (size_t i = 0, e = new_ops.size(); i != e; ++i)
        new_ops[i] = specialize(call.op(i));

    // check whether we can optimize tail recursion
    for (size_t i = stack_.size(); i-- != 0;) {
        const auto& context = stack_[i];
        if (new_ops.front() == context.old_entry()) {
            std::vector<size_t> cut;
            bool substitute = true;
            for (size_t i = 0, e = context.args.size(); i != e && substitute; ++i) {
                if (auto def = context.args[i]) {
                    substitute &= def == new_ops[i+1];
                    cut.push_back(i+1);
                }
            }

            if (substitute) {
                new_ops.front() = context.new_entry;
                return Call(new_ops.cut(cut));
            }
        }
        // TODO only do simple recursion for now
        break;
    }

    auto new_callee = new_ops.front();
    auto new_args = new_ops.skip_front();

    if (auto callee = new_callee->isa_continuation()) {
        if (callee->intrinsic() == Intrinsic::PeInfo) {
            assert(new_args[1]->type() == world().ptr_type(world().indefinite_array_type(world().type_pu8())));
            auto msg = new_args[1]->as<Bitcast>()->from()->as<Global>()->init()->as<DefiniteArray>();
            ILOG(new_callee, "pe_info: {}: {}", msg->as_string(), new_args[2]);
            auto next = new_args[3];
            return specialize_call(Call({next, new_args[0], world().tuple({})}));
        }

        if (!callee->empty()) {
            Call spec_call(new_ops.size());
            spec_call.callee() = callee;
            std::vector<const Def*> spec_ops;
            spec_ops.push_back(nullptr);

            bool fold = false;
            CondEval cond_eval(callee, new_args, top_level_);

            for (size_t i = 0, e = spec_call.num_args(); i != e; ++i) {
                if (cond_eval.eval(i)) {
                    fold = true;
                    spec_call.arg(i) = new_args[i];
                } else
                    spec_ops.emplace_back(new_args[i]);
            }

            //const auto& p = cache_.emplace(spec_call, nullptr);
            //Continuation*& target = p.first->second;
            // create new specialization if not found in cache
            //if (p.second)
                //target = drop(call);

            if (fold) {
                // TODO cache scope
                Scope scope(callee);
                spec_ops.front() = specialize_scope(scope, spec_call.args());

                return specialize_call(Call(spec_ops));
            }
        }
    }

    return Call(new_ops);
}

void PartialEvaluator::specialize_body(Continuation* old_continuation, Continuation* new_continuation) {
    auto call = specialize_call({old_continuation->ops()});
    new_continuation->jump(call.callee(), call.args(), old_continuation->jump_debug());
}

//------------------------------------------------------------------------------

void partial_evaluation(World& world) {
    world.cleanup();

    Scope::for_each(world, [&] (Scope& scope) {
        PartialEvaluator partial_evaluator(world);
        partial_evaluator.specialize_top_level(scope);
        scope.update();
    });

    //VLOG_SCOPE(PartialEvaluator(world).run());

    world.mark_pe_done();

    for (auto continuation : world.continuations())
        continuation->destroy_pe_profile();

    world.thorin();

    world.cleanup();
}

}
