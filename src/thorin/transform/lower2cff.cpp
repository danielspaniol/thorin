#include "thorin/continuation.h"
#include "thorin/world.h"
#include "thorin/analyses/cfg.h"
#include "thorin/analyses/verify.h"
#include "thorin/transform/mangle.h"
#include "thorin/util/log.h"

namespace thorin {

void lower2cff(World& world) {
    HashMap<Call, Continuation*> cache;
    auto top = world.top_continutions();

    bool local = true;
    for (bool todo = true; todo || local;) {
        todo = false;

        Scope::for_each(world, [&] (Scope& scope) {
            bool dirty = false;

            for (auto n : scope.f_cfg().post_order()) {
                auto continuation = n->continuation();
                if (auto callee = continuation->callee()->isa_continuation()) {
                    bool is_top = top.contains(callee);

                    auto is_bad = [&] (Continuation* callee) {
                        if (callee->empty())
                            return false;
                        if (local)
                            return scope.inner_contains(callee) && !callee->is_basicblock();
                        else {
                            if (is_top)
                                return !callee->is_returning() && !scope.contains(callee);
                            else
                                return !callee->is_basicblock();
                        }
                    };

                    if (!scope.contains(callee) && is_bad(callee)) {
                        DLOG("bad: {}: {} at {}", callee, callee->type(), callee->location());
                        todo = dirty = true;

                        Call call(continuation);
                        call.callee() = callee;
                        // it's fine to keep one higher-order arg for top-level continuations - guess the last one
                        size_t last = size_t(-1);
                        for (size_t i = 0, e = call.num_args(); i != e; ++i) {
                            if (callee->param(i)->order() > 0) {
                                call.arg(i) = continuation->arg(i);
                                last = i;
                            } else
                                call.arg(i) = nullptr;
                        }

                        if (is_top)
                            call.arg(last) = nullptr;

                        const auto& p = cache.emplace(call, nullptr);
                        Continuation*& target = p.first->second;
                        if (p.second)
                            target = drop(call); // use already dropped version as target

                        jump_to_cached_call(continuation, target, call);
                    }
                }
            }

            if (dirty)
                scope.update();
            top.insert(scope.entry());
        });

        if (!todo && local) {
            DLOG("switching to global mode");
            local = false;
            todo = true;
        }
    }

    debug_verify(world);
    world.cleanup();
}

}
