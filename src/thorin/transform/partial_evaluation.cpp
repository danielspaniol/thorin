#include "thorin/primop.h"
#include "thorin/world.h"
#include "thorin/analyses/cfg.h"
#include "thorin/analyses/free_defs.h"
#include "thorin/transform/mangle.h"
#include "thorin/util/hash.h"
#include "thorin/util/log.h"

namespace thorin {

class Env {
public:
    Env()
        : prev_(nullptr)
    {}
    Env(Env* prev)
        : prev_(prev)
    {}

    const Def* find(const Def* odef) {
        auto i = old2new_.find(odef);
        if (i != old2new_.end())
            return i->second;

        if (prev_ != nullptr)
            return prev_->find(odef);
        else
            return nullptr;
    }

    const Def* insert(const Def* odef, const Def* ndef) {
        auto p = old2new_.emplace(odef, ndef);
        assert_unused(p.second && "odef already as key in old2new_");
        return ndef;
    }

private:
    Env* prev_;
    Def2Def old2new_;
};

class Closure : public Def {
public:
    Closure(Env* env, Continuation* old_continuation)
        : Def(Node_Closure, old_continuation->type(), 0, {})
        , env_(env)
        , old_continuation_(old_continuation)
    {}

    Env* env() const { return env_; }
    Continuation* old_continuation() const { return old_continuation_; }
    Continuation* new_continuation() const { return new_continuation_; }

private:
    Env* env_;
    Continuation* old_continuation_;
    mutable Continuation* new_continuation_ = nullptr;

    friend class PartialEvaluator;
};

class PartialEvaluator {
public:
    PartialEvaluator(World& world)
        : world_(world)
    {}

    World& world() { return world_; }
    void run();
    Continuation* eval(Env* env, Continuation* continuation);
    const Def* materialize(Def2Def& old2new, const Def* odef);
    const Def* instantiate(Env* env, const Def* odef);
    void enqueue(Continuation* continuation) {
        if (done_.emplace(continuation).second)
            queue_.push(continuation);
    }
    void eat_pe_info(Continuation*);

private:
    World& world_;
    HashMap<Call, Continuation*> cache_;
    ContinuationSet done_;
    std::queue<Continuation*> queue_;
    ContinuationMap<bool> top_level_;
    std::deque<Env> envs_;
};

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
            Array<const Def*> nops(oprimop->num_ops());
            for (size_t i = 0; i != oprimop->num_ops(); ++i)
                nops[i] = instantiate(odef->op(i));

            auto nprimop = oprimop->rebuild(nops);
            return old2new_[oprimop] = nprimop;
        }

        return old2new_[odef] = odef;
    }

    bool eval(size_t i) {
        // the only higher order parameter that is allowed is a single 1st-order parameter of a top-level continuation
        // all other parameters need specialization (lower2cff)
        auto order = callee_->param(i)->order();
        if (order >= 2 || (order == 1 && (!callee_->is_returning() || !is_top_level(callee_)))) {
            DLOG("bad param({}) {} of continuation {}", i, callee_->param(i), callee_);
            return true;
        }

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

void PartialEvaluator::eat_pe_info(Continuation* cur) {
    assert(cur->arg(1)->type() == world().ptr_type(world().indefinite_array_type(world().type_pu8())));
    auto msg = cur->arg(1)->as<Bitcast>()->from()->as<Global>()->init()->as<DefiniteArray>();
    ILOG(cur->callee(), "pe_info: {}: {}", msg->as_string(), cur->arg(2));
    auto next = cur->arg(3);
    cur->jump(next, {cur->arg(0)}, cur->jump_debug());

    // always re-insert into queue because we've changed cur's jump
    queue_.push(cur);
}

void PartialEvaluator::run() {
    std::vector<Continuation*> externals;
    for (auto external : world().externals()) {
        externals.push_back(external);
        top_level_[external] = true;
    }

    for (auto old_external : externals) {
        Env env;
        auto new_external = eval(&env, old_external);
        new_external->make_external();
        old_external->destroy_body();
        old_external->replace(new_external);
    }
}

const Def* PartialEvaluator::instantiate(Env* env, const Def* odef) {
    if (auto ndef = env->find(odef))
        return ndef;

    if (auto oprimop = odef->isa<PrimOp>()) {
        Array<const Def*> nops(oprimop->num_ops());
        for (size_t i = 0; i != oprimop->num_ops(); ++i)
            nops[i] = instantiate(env, odef->op(i));

        auto nprimop = oprimop->rebuild(nops);
        return env->insert(oprimop, nprimop);
    }

    if (auto ocontinuation = odef->isa_continuation())
        return env->insert(odef, new Closure(env, ocontinuation));

    return env->insert(odef, odef);
}

const Def* PartialEvaluator::materialize(Def2Def& old2new, const Def* odef) {
    if (auto ndef = find(old2new, odef))
        return ndef;

    if (auto oprimop = odef->isa<PrimOp>()) {
        Array<const Def*> nops(oprimop->num_ops());
        for (size_t i = 0; i != oprimop->num_ops(); ++i)
            nops[i] = materialize(old2new, odef->op(i));

        auto nprimop = oprimop->rebuild(nops);
        return old2new[oprimop] = nprimop;
    }

    if (auto closure = odef->isa<Closure>()) {
        if (auto new_continuation = closure->new_continuation())
            return old2new[closure] = new_continuation;

        auto new_continuation = eval(closure->env(), closure->old_continuation());
        return old2new[odef] = closure->new_continuation_ = new_continuation;
    }

    return old2new[odef] = odef;
}

Continuation* PartialEvaluator::eval(Env* env, Continuation* continuation) {
    if (continuation->empty())
        return continuation;
    auto new_continuation = continuation->stub();
    for (size_t i = 0; i != new_continuation->num_params(); ++i)
        env->insert(continuation->param(i), new_continuation->param(i));

    Continuation* cur = continuation;

    while (true) {
        Call call(cur);

        for (size_t i = 0, e = call.num_ops(); i != e; ++i)
            call.op(i) = instantiate(env, cur->op(i));

        auto old_callee = call.callee()->isa_continuation();

        if (auto closure = call.callee()->isa<Closure>()) {
            env = closure->env();
            old_callee = closure->old_continuation();
        }

        if (old_callee != nullptr && !old_callee->empty()) {
            env = new Env(env);

            bool fold = false;
            CondEval cond_eval(old_callee, call.args(), top_level_);

            std::vector<const Type*> param_types;
            for (size_t i = 0, e = call.num_args(); i != e; ++i) {
                if (cond_eval.eval(i)) {
                    env->insert(old_callee->param(i), call.arg(i));
                    fold = true;
                } else
                    param_types.emplace_back(old_callee->param(i)->type());
            }

            if (fold) {
                auto fn_type = world().fn_type(param_types);
                auto new_callee = world().continuation(fn_type, old_callee->debug_history());

                // map old params to new params
                for (size_t i = 0, j = 0, e = call.num_args(); i != e; ++i) {
                    auto old_param = old_callee->param(i);
                    if (!cond_eval.eval(i)) {
                        auto new_param = new_callee->param(j++);
                        env->insert(old_param, new_param);
                        new_param->debug().set(old_param->name());
                    }
                }

                // TODO rewrite pe profile

                cur = new_callee;
                continue;
            }
        }

        // materialize closures
        Def2Def old2new;
        for (size_t i = 0, e = call.num_ops(); i != e; ++i)
            call.op(i) = materialize(old2new, call.op(i));

        new_continuation->jump(call.callee(), call.args(), continuation->jump_debug());
        return new_continuation;
    }
}

//------------------------------------------------------------------------------

void partial_evaluation(World& world) {
    world.cleanup();
    VLOG_SCOPE(PartialEvaluator(world).run());

    world.mark_pe_done();

    for (auto continuation : world.continuations())
        continuation->destroy_pe_profile();

    world.cleanup();
}

//------------------------------------------------------------------------------

}
