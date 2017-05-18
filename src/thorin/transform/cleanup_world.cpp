#include "thorin/world.h"
#include "thorin/analyses/cfg.h"
#include "thorin/analyses/scope.h"
#include "thorin/analyses/domtree.h"
#include "thorin/analyses/verify.h"
#include "thorin/transform/importer.h"

namespace thorin {

class Cleaner {
public:
    Cleaner(World& world)
        : world_(world)
    {}

    World& world() { return world_; }
    void cleanup();
    void eta_conversion();
    void unreachable_code_elimination();
    void eliminate_params();
    void rebuild();
    void verify_closedness();
    void within(const Def*);

private:
    World& world_;
    bool todo_ = true;
};

void Cleaner::eta_conversion() {
    for (bool todo = true; todo;) {
        todo = false;
        for (auto continuation : world().continuations()) {
            if (!continuation->empty()) {
                while (auto callee = continuation->callee()->isa_continuation()) {
                    if (callee->num_uses() == 1 && !callee->empty() && !callee->is_external()) {
                        for (size_t i = 0, e = continuation->num_args(); i != e; ++i)
                            callee->param(i)->replace(continuation->arg(i));
                        continuation->jump(callee->callee(), callee->args(), callee->jump_debug());
                        callee->destroy_body();
                        todo_ = todo = true;
                    } else
                        break;
                }

                if (continuation->callee()->isa<Param>() && !continuation->is_external()
                        && continuation->args() == continuation->params_as_defs()) {
                    continuation->replace(continuation->callee());
                    continuation->destroy_body();
                    todo_ = todo = true;
                }
            }
        }
    }
}

void Cleaner::unreachable_code_elimination() {
    ContinuationSet reachable;
    Scope::for_each<false>(world(), [&] (const Scope& scope) {
        DLOG("scope: {}", scope.entry());
        for (auto n : scope.f_cfg_smart().reverse_post_order())
            reachable.emplace(n->continuation());
    });

    for (auto continuation : world().continuations()) {
        if (!reachable.contains(continuation) && !continuation->empty()) {
            for (auto param : continuation->params())
                param->replace(world().bottom(param->type()));
            continuation->replace(world().bottom(continuation->type()));
            continuation->destroy_body();
            todo_ = true;
        }
    }
}

static bool is_used_higher_order(Continuation* continuation) {
    for (auto use : continuation->uses()) {
        if (use.index() != 0 || !use->isa<Continuation>())
            return true;
    }

    return false;
}

void Cleaner::eliminate_params() {
    ParamMap<const Def*> param2def;

    auto mark_dynamic = [&] (Continuation* continuation) {
        for (auto param : continuation->params())
            param2def[param] = param;
    };

    // all external continuations' params are dynamic ...
    for (auto continuation : world().externals())
        mark_dynamic(continuation);

    // ... and so are all continuations with an empty body or used in a higher-order context
    for (auto continuation : world().continuations()) {
        if (continuation->empty() || is_used_higher_order(continuation))
            mark_dynamic(continuation);
    }

    // fixed-point iteration to statically find out what a param is
    for (bool todo = true; todo;) {
        todo = false;

        for (auto continuation : world().continuations()) {
            if (auto callee = continuation->callee()->isa_continuation()) {
                for (size_t i = 0, e = callee->num_params(); i != e; ++i) {
                    auto def = continuation->arg(i);

                    // if it's a param - find its representative in param2def
                    if (auto param = def->isa<Param>()) {
                        auto i = param2def.find(param);
                        if (i == param2def.end())
                            continue;       // not handled yet - wait to next iteration
                        def = i->second;
                    }

                    // try to put it into the map
                    auto p = param2def.emplace(callee->param(i), def);
                    if (p.second)
                        todo = true;        // first entry
                    else {
                        auto i = p.first;   // could not insert - we already map to sth
                        if (def != i->second && i->second != i->first) {
                            i->second = i->first;
                            todo = true;
                        }
                    }
                }
            }
        }
    }

    // apply analysis info
    for (auto ocontinuation : world().copy_continuations()) {
        std::vector<size_t> proxy_idx, param_idx;
        bool is_higher_order = false;

        for (size_t i = 0, e = ocontinuation->num_params(); i != e; ++i) {
            auto param = ocontinuation->param(i);
            auto it = param2def.find(param);
            if (it == param2def.end()) {
                DLOG("dead: {}", param);
                proxy_idx.push_back(i);     // if param unused or maps to some unique value
            } else {
                is_higher_order |= param->order() > 0;
                auto mapped = it->second;
                if (param != mapped) {
                    DLOG("{} -> {}", param, mapped);
                    proxy_idx.push_back(i);
                } else
                    param_idx.push_back(i); // do nothing otherwise
            }
        }

        if (is_higher_order)
            continue; // don't do sth here: we might get probls due to lower2cff

        if (!proxy_idx.empty()) {
            auto ncontinuation = world().continuation(world().fn_type(ocontinuation->type()->ops().cut(proxy_idx)),
                    ocontinuation->cc(), ocontinuation->intrinsic(), ocontinuation->debug_history());

            // replace old params which must be kept with ncontinuation's ones
            size_t j = 0;
            for (auto i : param_idx) {
                ocontinuation->param(i)->replace(ncontinuation->param(j));
                ncontinuation->param(j++)->debug() = ocontinuation->param(i)->debug_history();
            }

            // replace old params with its according analysis info or do nothing if it is dead
            for (auto i : proxy_idx) {
                auto it = param2def.find(ocontinuation->param(i));
                if (it != param2def.end())
                    ocontinuation->param(i)->replace(it->second);
            }

            // wire ncontinuation into the program
            ncontinuation->jump(ocontinuation->callee(), ocontinuation->args(), ocontinuation->jump_debug());
            ocontinuation->destroy_body();

            for (auto use : ocontinuation->copy_uses()) {
                auto ucontinuation = use->as_continuation();
                assert(use.index() == 0);
                ucontinuation->jump(ncontinuation, ucontinuation->args().cut(proxy_idx), ucontinuation->jump_debug());
            }

            todo_ = true;
        }
    }
}

void Cleaner::rebuild() {
    Importer importer(world_.name());
    importer.type_old2new_.rehash(world_.types_.capacity());
    importer.def_old2new_.rehash(world_.primops().capacity());

#ifndef NDEBUG
    world_.swap_breakpoints(importer.world());
#endif

    for (auto external : world().externals())
        importer.import(external);

    swap(importer.world(), world_);
    todo_ |= importer.todo();
}

void Cleaner::verify_closedness() {
    auto check = [&](const Def* def) {
        size_t i = 0;
        for (auto op : def->ops()) {
            within(op);
            assert_unused(op->uses_.contains(Use(i++, def)) && "can't find def in op's uses");
        }

        for (const auto& use : def->uses_) {
            within(use);
            assert(use->op(use.index()) == def && "use doesn't point to def");
        }
    };

    for (auto primop : world().primops())
        check(primop);
    for (auto continuation : world().continuations()) {
        check(continuation);
        for (auto param : continuation->params())
            check(param);
    }
}

void Cleaner::within(const Def* def) {
    assert(world().types().contains(def->type()));
    if (auto primop = def->isa<PrimOp>())
        assert_unused(world().primops().contains(primop));
    else if (auto continuation = def->isa_continuation())
        assert_unused(world().continuations().contains(continuation));
    else
        within(def->as<Param>()->continuation());
}

void Cleaner::cleanup() {
#ifndef NDEBUG
    for (const auto& p : world().trackers_)
        assert(p.second.empty() && "there are still live trackers before running cleanup");
#endif

    int i = 0;
    for (; todo_; ++i) {
        todo_ = false;
        eta_conversion();
        eliminate_params();
        unreachable_code_elimination();
        rebuild();
    }
    DLOG("fixed-point reached after {} iterations", i);

#ifndef NDEBUG
    verify_closedness();
    debug_verify(world());
#endif
}

void cleanup_world(World& world) { Cleaner(world).cleanup(); }

}
