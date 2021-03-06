#include "thorin/world.h"
#include "thorin/analyses/scope.h"

namespace thorin {

void codegen_prepare(World& world) {
    const Param* old_param = nullptr;
    const Def* new_param = nullptr;

    world.rewrite("codegen_prepare",
        [&](const Scope& scope) {
            if (auto entry = scope.entry()->isa<Lam>();
                     entry && entry->type()->is_cn()) {
                // new wrapper that calls the return continuation
                old_param = entry->param();
                auto ret_param = entry->ret_param();
                auto ret_cont = world.lam(ret_param->type()->as<Pi>(), ret_param->debug());
                ret_cont->app(ret_param, ret_cont->param(), ret_param->debug());

                // rebuild a new "param" that substitutes the actual ret_param with ret_cont
                auto ops = entry->param()->split();
                assert(ops.back() == ret_param && "we assume that the last element is the ret_param");
                ops.back() = ret_cont;
                new_param = world.tuple(ops);
                return true;
            }
            return false;
        },
        [&](const Def* old_def) -> const Def* {
            if (old_def == old_param) return new_param;
            return nullptr;
        });
}

}
