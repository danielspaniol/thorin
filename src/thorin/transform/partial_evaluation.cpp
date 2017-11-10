#include "thorin/primop.h"
#include "thorin/world.h"
#include "thorin/analyses/cfg.h"
#include "thorin/analyses/free_defs.h"
#include "thorin/transform/mangle.h"
#include "thorin/util/hash.h"
#include "thorin/util/log.h"

namespace thorin {

class PartialEvaluator {
public:
    PartialEvaluator(World& world)
        : world_(world)
    {}

    World& world() { return world_; }
    bool run();
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
};

class CondEval {
public:
    CondEval(Continuation* callee, Defs args)
        : callee_(callee)
        , args_(args)
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
        return (callee_->num_uses() == 1 && !callee_->is_external()) || is_one(instantiate(pe_profile(i)));
    }

    const Def* pe_profile(size_t i) {
        return callee_->pe_profile().empty() ? world().literal_bool(false, {}) : callee_->pe_profile(i);
    }

private:
    Continuation* callee_;
    Defs args_;
    Def2Def old2new_;
};

void PartialEvaluator::eat_pe_info(Continuation* cur) {
    assert(cur->arg(1)->type() == world().ptr_type(world().indefinite_array_type(world().type_pu8())));
    auto next = cur->arg(3);

    if (is_const(cur->arg(2))) {
        auto msg = cur->arg(1)->as<Bitcast>()->from()->as<Global>()->init()->as<DefiniteArray>();
        ILOG(cur->callee(), "pe_info: {}: {}", msg->as_string(), cur->arg(2));
        cur->jump(next, {cur->arg(0)}, cur->jump_debug());

        // always re-insert into queue because we've changed cur's jump
        queue_.push(cur);
    } else if (auto continuation = next->isa_continuation()) {
        queue_.push(continuation);
    }
}

bool PartialEvaluator::run() {
    bool todo = false;

    for (auto external : world().externals())
        enqueue(external);

    while (!queue_.empty()) {
        auto continuation = pop(queue_);

        bool force_fold = false;
        auto callee_def = continuation->callee();

        if (auto run = continuation->callee()->isa<Run>()) {
            force_fold = true;
            callee_def = run->def();
        }

        if (auto callee = callee_def->isa_continuation()) {
            if (callee->intrinsic() == Intrinsic::PeInfo) {
                eat_pe_info(continuation);
                continue;
            }

            if (!callee->empty()) {
                Call call(continuation->num_ops());
                call.callee() = callee;

                CondEval cond_eval(callee, continuation->args());

                bool fold = false;
                for (size_t i = 0, e = call.num_args(); i != e; ++i) {
                    if (force_fold || cond_eval.eval(i)) {
                        call.arg(i) = continuation->arg(i);
                        fold = true;
                    } else
                        call.arg(i) = nullptr;
                }

                if (fold) {
                    const auto& p = cache_.emplace(call, nullptr);
                    Continuation*& target = p.first->second;
                    // create new specialization if not found in cache
                    if (p.second) {
                        target = drop(call);
                        todo = true;
                    }

                    jump_to_dropped_call(continuation, target, call);
                }
            }
        }

        for (auto succ : continuation->succs())
            enqueue(succ);
    }

    return todo;
}

//------------------------------------------------------------------------------

bool partial_evaluation(World& world) {
    VLOG("start pe");
    auto res = PartialEvaluator(world).run();
    VLOG("end pe");
    return res;
}

//------------------------------------------------------------------------------

}
