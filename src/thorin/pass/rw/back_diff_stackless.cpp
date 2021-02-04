#include "thorin/pass/rw/back_diff_stackless.h"

#include "thorin/rewrite.h"

namespace thorin {

////////////////////////////////////////////////////////////////////////////////
// Actual algorithm
////////////////////////////////////////////////////////////////////////////////

namespace {

class Algo {
  public:
    Algo(World &world, Lam *fn);

    Lam *rewrite();

  private:
    const Def *primal(const Def *def, const Def *back);

    Lam *primal_bb(Lam *bb);
    Lam *pullback_bb(Lam *bb);
    Lam *adjoint_bb(Lam *bb);

    const Pi *primal_bb_pi(Lam *bb);
    const Pi *pullback_bb_pi(Lam *bb);
    const Pi *adjoint_bb_pi(Lam *bb);
    const Pi *back_cn_pi(const Pi *pi);

    const Def *back_var(Lam *bb);
    const Sigma *add_to(const Def *target, const Def *def);
    const Pi *add_to_dom(const Pi *pi, const Def *param);

    void src2dst_params(Lam *src, Lam *dst);

    World &world_;
    const Pi *pullback_ret_pi_;
    Def2Def src2primal_;
    Def2Def primal2back_;
    Def2Def primal2pullback_;
    Def2Def primal2adjoint_;
};

Algo::Algo(World &world, Lam *fn)
    : world_{world}, pullback_ret_pi_{
                         world_.cn(fn->type()->dom()->ops().skip_back())} {}

const Def *Algo::primal(const Def *def, const Def *back) {
    if (src2primal_.contains(def)) {
        return src2primal_[def];
    }

    if (auto lam = def->isa_nom<Lam>()) {
        if (lam->is_basicblock()) {
            return primal_bb(lam);
        } else {
            // TODO: Function calls
        }
    }

    if (auto app = def->isa<App>()) {
        auto callee = app->callee();

        if (callee->type()->as<Pi>()->is_cn()) {
            auto primal_callee = primal(callee, back);
            auto primal_arg = primal(app->arg(), back);

            auto calls_primal = callee->type() != primal_callee->type();
            if (calls_primal) {
                primal_arg = add_to(primal_arg, back);
            }

            return world_.app(primal_callee, primal_arg, app->dbg());
        }

        // TODO: Direct Style Calls
    }

    if (auto tuple = def->isa<Tuple>()) {
        auto ops = tuple->ops();
        Array<const Def *> primal_ops(ops.size(), [this, back, &ops](auto i) {
            return primal(ops[i], back);
        });

        return world_.tuple(primal_ops, tuple->dbg());
    }

    if (auto pack = def->isa<Pack>()) {
        auto primal_body = primal(pack->body(), back);
        auto primal_shape = primal(pack->shape(), back);

        return world_.pack(primal_body, primal_shape, pack->dbg());
    }

    if (auto extract = def->isa<Extract>()) {
        auto primal_tuple = primal(extract->tuple(), back);
        auto primal_index = primal(extract->index(), back);

        return world_.extract(primal_tuple, primal_index, extract->dbg());
    }

    if (auto insert = def->isa<Insert>()) {
        auto primal_tuple = primal(insert->tuple(), back);
        auto primal_index = primal(insert->index(), back);
        auto primal_value = primal(insert->value(), back);

        return world_.insert(primal_tuple, primal_index, primal_value,
                             insert->dbg());
    }

    if (auto axiom = def->isa<Axiom>()) {
        switch (axiom->tag()) {
        case Tag::ROp: { // TODO: is this the correct place?
        }
        case Tag::Load: { // TODO: Loads and stores
        }
        case Tag::Store: { // TODO: Loads and stores
        }
        }
    }

    return def;
}

Lam *Algo::primal_bb(Lam *bb) {
    if (src2primal_.contains(bb)) {
        return src2primal_[bb]->as_nom<Lam>();
    }

    auto new_bb = world_.nom_lam(primal_bb_pi(bb),
                                 world_.dbg({"primal_" + bb->debug().name}));
    src2dst_params(bb, new_bb);
    src2primal_[bb] = new_bb;

    auto back = back_var(new_bb);
    primal2back_[new_bb] = back;
    primal2adjoint_[new_bb] = adjoint_bb(bb);
    primal2pullback_[new_bb] = pullback_bb(bb);

    new_bb->set_filter(false);
    new_bb->set_body(primal(bb->body(), back));
    return new_bb;
}

Lam *Algo::pullback_bb(Lam *bb) {
    auto new_bb = world_.nom_lam(pullback_bb_pi(bb),
                                 world_.dbg({"pullback_" + bb->debug().name}));
    src2dst_params(bb, new_bb);
    src2primal_[bb] = new_bb;

    auto args = add_to(new_bb->var(), back_var(bb));
    auto adjoint = primal2adjoint_[src2primal_[bb]]; // TODO: this is ugly...

    new_bb->set_filter(false);
    new_bb->set_body(world_.app(adjoint, args));
    return new_bb;
}

Lam *Algo::adjoint_bb(Lam *bb) {
    auto new_bb = world_.nom_lam(adjoint_bb_pi(bb),
                                 world_.dbg({"adjoint_" + bb->debug().name}));
    src2dst_params(bb, new_bb);
    src2primal_[bb] = new_bb;

    new_bb->set_filter(false);
    return new_bb;
}

const Pi *Algo::primal_bb_pi(Lam *bb) {
    return add_to_dom(bb->type(), back_cn_pi(bb->type()));
}

const Pi *Algo::pullback_bb_pi(Lam *bb) {
    if (auto app = bb->body()->isa<App>()) {
        // TODO: I think this only works for basicblocks.
        return back_cn_pi(app->callee()->type()->as<Pi>());
    }

    // TODO: Direct style function?
    THORIN_UNREACHABLE;
}

const Pi *Algo::adjoint_bb_pi(Lam *bb) {
    return add_to_dom(pullback_bb_pi(bb), back_cn_pi(bb->type()));
}

const Pi *Algo::back_cn_pi(const Pi *pi) {
    return add_to_dom(pi, pullback_ret_pi_);
}

const Def *Algo::back_var(Lam *bb) {
    if (primal2back_.contains(bb)) {
        return primal2back_[bb];
    }
    return bb->var(bb->num_vars() - 1, world_.dbg("back"));
}

const Sigma *Algo::add_to(const Def *target, const Def *def) {
    if (target->isa<Sigma>()) {
        auto ops = target->ops();
        Array<const Def *> new_ops(ops.size() + 1, [&ops, def](auto i) {
            return i < ops.size() ? ops[i] : def;
        });
        return world_.sigma(new_ops, target->dbg())->as<Sigma>();
    } else {
        return world_.sigma({target, def}, target->dbg())->as<Sigma>();
    }
}

const Pi *Algo::add_to_dom(const Pi *pi, const Def *param) {
    return world_.pi(add_to(pi->dom(), param), pi->dbg());
}

void Algo::src2dst_params(Lam *src, Lam *dst) {
    for (size_t i = 0, e = src->num_vars(); i < e; ++i) {
        auto src_var = src->var(i);
        auto dst_var = dst->var(i, src_var->dbg());
        src2primal_[src_var] = dst_var;
    }
}

} // namespace

////////////////////////////////////////////////////////////////////////////////
// Interface
////////////////////////////////////////////////////////////////////////////////

static Lam *isa_lam_for_backdiff(const Def *def) {
    if (auto outer_app = def->isa<App>()) {
        if (auto inner_app = outer_app->callee()->isa<App>()) {
            if (auto ax = inner_app->callee()->isa<Axiom>()) {
                if (ax->tag() == Tag::BckDiff) {
                    return outer_app->arg()->as_nom<Lam>();
                }
            }
        }
    }

    return nullptr;
}

const Def *BackDiff::rewrite(const Def *def) {
    if (auto lam = isa_lam_for_backdiff(def)) {
        return Algo(world(), lam).rewrite();
    }
}

} // namespace thorin
