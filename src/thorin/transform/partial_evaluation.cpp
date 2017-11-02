#include "thorin/primop.h"
#include "thorin/world.h"
#include "thorin/analyses/cfg.h"
#include "thorin/analyses/free_defs.h"
#include "thorin/transform/importer.h"
#include "thorin/transform/mangle.h"
#include "thorin/util/hash.h"
#include "thorin/util/log.h"

// TODO pe_info

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
    ContinuationMap<bool>& top_level_;
};

class Env : public Streamable {
public:
    Env(Env* parent)
        : parent_(parent)
    {}

    const Def* insert_old2tmp(const Def* old_def, const Def* tmp_def) {
        auto p = old2tmp_.emplace(old_def, tmp_def);
        assert_unused(p.second && "old_def already as key in old2tmp_");
        return tmp_def;
    }
    const Def* insert_tmp2new(const Def* tmp_def, const Def* new_def) {
        auto p = tmp2new_.emplace(tmp_def, new_def);
        assert_unused(p.second && "tmp_def already as key in tmp2new_");
        return new_def;
    }

    const Def* find_old2tmp(const Def* old_def) const {
        auto i = old2tmp_.find(old_def);
        if (i != old2tmp_.end())
            return i->second;

        if (parent_ != nullptr)
            return parent_->find_old2tmp(old_def);
        else
            return nullptr;
    }
    const Def* find_tmp2new(const Def* tmp_def) const {
        auto i = tmp2new_.find(tmp_def);
        if (i != tmp2new_.end())
            return i->second;

        if (parent_ != nullptr)
            return parent_->find_tmp2new(tmp_def);
        else
            return nullptr;
    }

    virtual std::ostream& stream(std::ostream& o) const {
        o << "{";
        auto print = [&] (const auto& elem) { o << elem.first << ": " << elem.second; };
        stream_list(o, old2tmp_, print, " o2t{", "}, ");
        stream_list(o, tmp2new_, print, "t2n{", "}");
        return o << "}";
    }

private:
    Env* parent_;
    Def2Def old2tmp_;
    Def2Def tmp2new_;

    friend class PartialEvaluator;
};

class Context {
public:
    Context() {}
    Context(Env* parent_env)
        : env_(std::make_unique<Env>(parent_env))
        , num_uses_(1)
    {}

    Continuation* new_continuation() const { return new_continuation_; }
    Env* env() const { return env_.get(); }
    int num_uses() const { return num_uses_; }
    void inc_uses() const { ++num_uses_; }

    friend void swap(Context& c1, Context& c2) {
        using std::swap;
        swap(c1.new_continuation_, c2.new_continuation_);
        swap(c1.env_,              c2.env_);
        swap(c1.num_uses_,         c2.num_uses_);
    }

private:
    Continuation* new_continuation_ = nullptr;
    std::unique_ptr<Env> env_;
    mutable int num_uses_;

    friend class PartialEvaluator;
};

class Closure : public Def {
private:
    struct ArgsHash {
        static uint64_t hash(Defs args) {
            auto hash = hash_begin();
            for (auto arg : args)
                hash = hash_combine(hash, arg ? arg->gid() : 0);
            return hash;
        }
        static bool eq(Defs args1, Defs args2) { return args1 == args2; }
        static Array<const Def*> sentinel() { return Array<const Def*>(); }
    };

public:
    Closure(Env* parent_env, Continuation* continuation)
        : Def(Node_Closure, continuation->type(), 0, {})
        , parent_env_(parent_env)
        , continuation_(continuation)
    {
        parent_env->insert_old2tmp(continuation, this);
    }

    Continuation* continuation() const { return continuation_; }

    Context* add_context(Defs args) const {
        outf("add context for {} with args: ", continuation_);
        stream_list(std::cout, args, [](auto e) { std::cout << e; }, "[", "]\n");
        auto p = args2context_.emplace(Array<const Def*>(args), std::make_unique<Context>(parent_env_));
        auto context = p.first->second.get();
        if (!p.second)
            context->inc_uses();
        else {
            auto env = context->env();
            for (size_t i = 0, e = args.size(); i != e; ++i) {
                if (args[i] != nullptr)
                    env->insert_old2tmp(continuation()->param(i), args[i]);
            }
        }
        return context;
    }

    Context* get_context(Defs args) const {
        auto i = args2context_.find(args);
        assert(i != args2context_.end());
        return i->second.get();
    }

    virtual std::ostream& stream(std::ostream& o) const { return o << unique_name() << "(" << continuation() << ")"; }

private:
    Env* parent_env_;
    Continuation* continuation_;
    mutable HashMap<Array<const Def*>, std::unique_ptr<Context>, ArgsHash> args2context_;

    friend class PartialEvaluator;
};

class PartialEvaluator {
private:
    struct Todo {
    public:
        Todo() = delete;
        Todo(const Todo&) = delete;
        Todo(Todo&&) = delete;

        Todo(Continuation* old_calling_continuation, Continuation* new_calling_continuation, Array<const Def*>&& tmp_ops)
            : old_calling_continuation_(old_calling_continuation)
            , new_calling_continuation_(new_calling_continuation)
            , tmp_ops_(std::move(tmp_ops))
        {}

        const Closure* closure() const { return tmp_ops_.front()->as<Closure>(); }
        Defs args() const { return tmp_ops_.skip_front(); }
        Continuation* old_calling_continuation() const { return old_calling_continuation_; }
        Continuation* new_calling_continuation() const { return new_calling_continuation_; }

    private:
        Continuation* old_calling_continuation_;
        Continuation* new_calling_continuation_;
        Array<const Def*> tmp_ops_;

        friend class PartialEvaluator;
    };

public:
    PartialEvaluator(World& old_world)
        : old_world_(old_world)
        , importer_(old_world)
        , indent(0)
    {}

    World& old_world() { return old_world_; }
    World& new_world() { return importer_.world(); }
    void run();

private:
    void eval(const Closure* closure, Env* env, Defs args);
    const Def* materialize(Def2Def& old2new, const Def* odef);
    const Def* specialize(Env* env, const Def* odef);
    Continuation* residualize(Continuation* old_calling_continuation, Continuation* new_calling_continuation, const Closure* closure, Env* calling_env, Defs args);
    const Def* residualize(Env* env, const Def* tmp_def);

    void eat_pe_info(Continuation*);
    const Closure* create_closure(Env* env, Continuation* continuation) {
        closures_.emplace_back(env, continuation);
        outf("creating closure {} for continuation {} in env {}\n", closures_.back().gid(), continuation, env);
        return &closures_.back();
    }

    void enqueue(Continuation* old_calling_continuation, Continuation* new_calling_continuation, Array<const Def*>&& tmp_ops) {
        queue_.emplace(old_calling_continuation, new_calling_continuation, std::move(tmp_ops));
    }

    const Type* import(const Type* old_type) { return importer_.import(old_type); }

    template<typename... Args>
    std::ostream& outf(const char* fmt, Args... args) {
        for (size_t i = 0; i < indent; i++)
            std::cout << "  ";
        return streamf(std::cout, fmt, std::forward<Args>(args)...);
    }

    World& old_world_;
    Importer importer_;
    std::queue<Todo> queue_;
    ContinuationMap<bool> top_level_;
    std::deque<Closure> closures_;
    size_t indent;
};

void PartialEvaluator::run() {
    old_world().dump();
    Env root_env(nullptr);
    for (auto external : old_world().externals()) {
        outf("--PE: {}\n", external);
        auto new_continuation = residualize(nullptr, nullptr, create_closure(&root_env, external), nullptr,
                                            Array<const Def*>(external->num_params()));
        new_continuation->make_external();

        while (!queue_.empty()) {
            auto& todo = queue_.front();
            auto closure = todo.closure();
            auto args = todo.args();
            auto context = closure->get_context(args);
            outf("-TODO: {} #uses {} for args: ", closure->continuation(), context->num_uses());
            stream_list(std::cout, args, [](auto e) { std::cout << e; }, "[", "]\n");
            if (context->num_uses() == 1) {
                context->new_continuation_ = todo.new_calling_continuation();
                eval(closure, context->env(), args);
            } else
                // TODO check whether we used num_uses==1 branch for this context already
                residualize(todo.old_calling_continuation(), todo.new_calling_continuation(), closure,
                            context->env(), args);
            queue_.pop();
        }
    }

    new_world().dump();

    new_world().mark_pe_done();

    for (auto continuation : old_world().continuations())
        continuation->destroy_pe_profile();

    new_world().cleanup();
    swap(new_world(), old_world());
}

void PartialEvaluator::eval(const Closure* closure, Env* env, Defs args) {
    auto closure_context = closure->get_context(args);
    auto new_continuation = closure_context->new_continuation();
    auto old_continuation = closure->continuation();
    assert(new_continuation != nullptr);
    indent++;
    outf("eval {} with args: ", old_continuation);
    stream_list(std::cout, args, [](auto e) { std::cout << e; }, "[", "]\n");

    Array<const Def*> tmp_ops(old_continuation->num_ops(), [&] (auto i) {
        return specialize(env, old_continuation->op(i));
    });

    if (auto callee_closure = tmp_ops.front()->isa<Closure>()) {
        auto callee_continuation = callee_closure->continuation();
        switch (callee_continuation->intrinsic()) {
            case Intrinsic::Branch: {
                if (auto lit = tmp_ops[1]->isa<PrimLit>()) {
                    tmp_ops[0] = lit->value().get_bool() ? tmp_ops[2] : tmp_ops[3];
                    tmp_ops.shrink(1);
                    outf("folding branch with {} to {}\n", lit, tmp_ops[0]);
                }
                break;
            }
            case Intrinsic::Match:
                if (old_continuation->num_args() == 2) {
                    tmp_ops.shrink(1);
                    break;
                }

                if (auto lit = tmp_ops[1]->isa<PrimLit>()) {
                    for (size_t i = 2; i < old_continuation->num_args(); i++) {
                        if (old_world().extract(tmp_ops[i+1], 0_s)->as<PrimLit>() == lit) {
                            tmp_ops[0] = old_world().extract(tmp_ops[i+1], 1);
                            tmp_ops.shrink(1);
                            break;
                        }
                    }
                }
                break;
            default:
                break;
        }
    }

    if (auto callee_closure = tmp_ops.front()->isa<Closure>()) {
        auto callee_continuation = callee_closure->continuation();
        auto args = tmp_ops.skip_front();
        if (!callee_continuation->empty()) {
            CondEval cond_eval(callee_continuation, args, top_level_);
            std::vector<const Type*> param_types;
            bool fold = false;
            for (size_t i = 0, e = args.size(); i != e; ++i) {
                if (cond_eval.eval(i)) {
                    fold = true;
                } else
                    param_types.emplace_back(callee_continuation->param(i)->type());
            }

            if (fold) {
                outf("queueing {} with args: ", callee_continuation);
                stream_list(std::cout, args, [](auto e) { std::cout << e; }, "[", "]\n");

                auto c = callee_closure->add_context(args);

                for (auto p : env->tmp2new_) {
                    c->env()->insert_tmp2new(p.first, p.second);
                }
                enqueue(old_continuation, new_continuation, std::move(tmp_ops));
                indent--;
                return;
            }
        }
        residualize(old_continuation, new_continuation, callee_closure, env, Array<const Def*>(args.size()));
    } else {
        assert(new_continuation->ops().empty());
        Array<const Def*> new_ops(old_continuation->num_ops());
        for (size_t i = 0, e = new_ops.size(); i != e; ++i) {
            new_ops[i] = residualize(env, tmp_ops[i]);
        }

        new_continuation->jump(new_ops.front(), new_ops.skip_front(), old_continuation->jump_debug());
    }
    indent--;
}

const Def* PartialEvaluator::specialize(Env* env, const Def* old_def) {
    assert(!old_def->isa<Closure>());

    if (auto tmp_def = env->find_old2tmp(old_def))
        return tmp_def;

    if (auto old_primop = old_def->isa<PrimOp>()) {
        Array<const Def*> tmp_ops(old_primop->num_ops());
        for (size_t i = 0; i != old_primop->num_ops(); ++i)
            tmp_ops[i] = specialize(env, old_def->op(i));

        auto tmp_primop = old_primop->rebuild(tmp_ops);
        return env->insert_old2tmp(old_primop, tmp_primop);
    }

    if (auto old_continuation = old_def->isa_continuation())
        return create_closure(env, old_continuation);

    return old_def;
}

// builds a call within new_calling_continuation (former old_calling_continuation) calling closure with args
// we need to be absolutely sure that we want to build this call before invoking this
// args[i] == x:       this must be baked into the closure's corresponding context->env
// args[i] == nullptr: this is a residual old_calling_continuation->arg(i)
Continuation* PartialEvaluator::residualize(Continuation* old_calling_continuation, Continuation* new_calling_continuation, const Closure* closure, Env* calling_env, Defs args) {
    auto callee = closure->continuation();
    indent++;
    outf("residualize {} in {} for args: ", callee, old_calling_continuation);
    stream_list(std::cout, args, [](auto e) { std::cout << e; }, "[", "]\n");
    auto context = closure->add_context(args);

    auto& new_continuation = context->new_continuation_;
    if (new_continuation == nullptr) {
        if (callee->empty()) {
            new_continuation = importer_.import(callee)->as_continuation();
        } else {
            std::vector<const Type*> new_param_types;
            for (size_t i = 0, e = args.size(); i != e; ++i) {
                if (args[i] == nullptr)
                    new_param_types.emplace_back(import(callee->param(i)->type()));
            }

            auto fn_type = new_world().fn_type(new_param_types);
            new_continuation = new_world().continuation(fn_type, callee->debug_history());

            for (size_t i = 0, j = 0, e = args.size(); i != e; ++i) {
                if (args[i] == nullptr) {
                    auto old_param = callee->param(i);
                    auto new_param = new_continuation->param(j++);
                    context->env()->insert_tmp2new(old_param, new_param);
                    new_param->debug() = old_param->debug_history();
                }
            }
            outf("-> built new continuation head ");
            new_continuation->dump_head();

            eval(closure, context->env(), args);
        }
    } else
        outf("-> nothing to do, already residualized\n");

    if (new_calling_continuation != nullptr) {
        Array<const Def*> new_args(new_continuation->num_params());
        for (size_t i = 0, j = 0, e = new_args.size(); i != e; ++i) {
            if (args[i] == nullptr) {
                auto old_arg = old_calling_continuation->arg(i);
                auto tmp_arg = calling_env->find_old2tmp(old_arg);
                if (tmp_arg == nullptr)
                    tmp_arg = old_arg;
                new_args[j++] = residualize(calling_env, tmp_arg);
            }
        }

        new_calling_continuation->jump(new_continuation, new_args, old_calling_continuation->jump_debug());

        outf("built jump to {} in {} with new args: ", new_continuation, new_calling_continuation);
        stream_list(std::cout, new_args, [](auto e) { std::cout << e; }, "[", "]\n");
    }

    indent--;
    return new_continuation;
}

const Def* PartialEvaluator::residualize(Env* env, const Def* tmp_def) {
    assert(!tmp_def->isa<Continuation>());

    if (auto new_def = env->find_tmp2new(tmp_def))
        return new_def;

    assertf(!tmp_def->isa<Param>(), "param {} must have been built in the new world already when building their continuation", tmp_def);

    if (auto tmp_primop = tmp_def->isa<PrimOp>()) {
        Array<const Def*> new_ops(tmp_primop->num_ops());
        for (size_t i = 0; i != tmp_primop->num_ops(); ++i)
            new_ops[i] = residualize(env, tmp_def->op(i));

        auto new_primop = tmp_primop->rebuild(new_world(), new_ops, import(tmp_primop->type()));
        return env->insert_tmp2new(tmp_primop, new_primop);
    }

    if (auto tmp_closure = tmp_def->isa<Closure>()) {
        return residualize(nullptr, nullptr, tmp_closure, nullptr, Array<const Def*>(tmp_closure->continuation()->num_params()));
    }
    THORIN_UNREACHABLE;
}

#if 0
void PartialEvaluator::eat_pe_info(Continuation* cur) {
    assert(cur->arg(1)->type() == world().ptr_type(world().indefinite_array_type(world().type_pu8())));
    auto msg = cur->arg(1)->as<Bitcast>()->from()->as<Global>()->init()->as<DefiniteArray>();
    ILOG(cur->callee(), "pe_info: {}: {}", msg->as_string(), cur->arg(2));
    auto next = cur->arg(3);
    cur->jump(next, {cur->arg(0)}, cur->jump_debug());

    // always re-insert into queue because we've changed cur's jump
    queue_.push(cur);
}

#endif

//------------------------------------------------------------------------------

void partial_evaluation(World& world) {
    world.cleanup();
    VLOG_SCOPE(PartialEvaluator(world).run());
}

//------------------------------------------------------------------------------

}
