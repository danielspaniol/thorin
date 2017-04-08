#include <algorithm>

#include "thorin/analyses/cfg.h"
#include "thorin/analyses/free_defs.h"
#include "thorin/analyses/scope.h"
#include "thorin/transform/mangle.h"
#include "thorin/util/log.h"

namespace thorin {

void higher_order_lifting(World& world) {
    auto top = world.top_continutions();

    Scope::for_each(world, [&](Scope& scope) {
        DLOG("scope: {}", scope.entry());
        bool dirty = false;

        for (auto n : scope.f_cfg().post_order()) {
            auto continuation = n->continuation();
            if (continuation != scope.entry() && continuation->order() > 1) {
                DLOG("lift: {}", continuation);
                Scope cur(continuation);
                auto free_defs = thorin::free_defs(cur);

                for (auto use : continuation->copy_uses()) {
                    if (auto caller = use->isa_continuation()) {
                        if (use.index() == 0 && !cur.contains(use)) {
                            auto fd = free_defs;
                            for (size_t i = 0; i != caller->num_args(); ++i)
                                fd.erase(caller->arg(i));

                            std::vector<const Def*> defs;
                            for (auto def : fd) {
                                if (!def->isa<Continuation>() || !top.contains(def->as_continuation())) {
                                    DLOG("free def: {}", def);
                                    defs.push_back(def);
                                }
                            }

                            Array<const Def*> empty(continuation->num_params());
                            Mangler mangler(cur, empty, defs);
                            auto lifted = mangler.mangle_head();

                            for (size_t i = 0; i != caller->num_args(); ++i)
                                mangler.def2def_[caller->arg(i)] = lifted->param(i);

                            mangler.mangle_body();
                            top.emplace(lifted);
                            caller->jump(lifted, concat(caller->args(), defs), caller->jump_debug());
                            dirty = true;
                        }
                    }
                }

            }
        }

        if (dirty)
            scope.update();
    });
}

}
