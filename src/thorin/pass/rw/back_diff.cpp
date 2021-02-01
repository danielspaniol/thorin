#include "thorin/pass/rw/back_diff.h"

#include "thorin/rewrite.h"

namespace thorin {

////////////////////////////////////////////////////////////////////////////////
// Finding functions to apply back_diff to
////////////////////////////////////////////////////////////////////////////////

namespace {

struct BackDiffApp {
    const Def *domain;
    const Def *codomain;
    Lam *fn;
};

// Calls to the back_diff axiom always have the form
//    app (app (back_diff, [domain, codomain]) fn)
std::optional<BackDiffApp> isa_backdiff_app(const Def *def) {
    if (auto outer_app = def->isa<App>()) {
        if (auto inner_app = outer_app->callee()->isa<App>()) {
            if (auto ax = inner_app->callee()->isa<Axiom>()) {
                if (ax->tag() == Tag::BckDiff) {
                    auto [dom, codom] = inner_app->args<2>();
                    auto fn = outer_app->arg()->as_nom<Lam>();
                    return {{dom, codom, fn}};
                }
            }
        }
    }

    return {};
}

////////////////////////////////////////////////////////////////////////////////
// Actual back_diff implementation
////////////////////////////////////////////////////////////////////////////////

class BackDiffImpl {
  public:
    BackDiffImpl(World &world, Lam *src, Lam *dst)
        : world_(world), src_(src), dst_(dst),
          pb_(world_.nom_lam(dst_->ret_var()->type()->as<Pi>(),
                             world_.dbg("PB_" + src_->debug().name))) {}

    Lam *rewrite();

  private:
    const Def *primal(const Def *src);
    void fill_pb();
    const Def *adjoint(const Def *primal);
    void fill_params();
    const Def *J_wrap_ROp(ROp op);

    World &world_;
    Lam *src_;
    Lam *dst_;
    Lam *pb_;
    Def2Def src2primal_;
    Def2Def primal2adjoint_;
};

Lam *BackDiffImpl::rewrite() {
    fill_params();
    fill_pb();
    primal(src_);

    return dst_;
}

void BackDiffImpl::fill_params() {
    for (size_t i = 0, e = src_->num_vars(); i < e; ++i) {
        auto src_var = src_->var(i);
        auto dst_var = dst_->var(i, world_.dbg(src_var->debug().name));
        src2primal_[src_var] = dst_var;
    }
}

const Def *BackDiffImpl::primal(const Def *src) {
    if (src == src_->ret_var()) {
        // TODO: change ret
    }

    if (src2primal_.contains(src)) {
        return src;
    }

    if (auto app = src->isa<App>()) {
        // TODO: Type of old an new callee are different -> Function call or
        // axiom call

        auto primal_callee = primal(app->callee());
        auto primal_arg = primal(app->arg());
        auto primal_app = world_.app(primal_callee, primal_arg, app->dbg());
        src2primal_[app] = primal_app;
        return primal_app;
    }

    if (auto lam = src->isa_nom<Lam>()) {
        if (lam->is_basicblock()) {
            auto cn_call = lam->body()->as<App>();
            auto primal_cn = primal(cn_call->callee());

            auto adjoint_cn = adjoint(primal_cn);
            primal2adjoint_[primal_cn] = adjoint_cn;

            auto mem = lam->mem_var();
            auto mem2 = world_.back_diff_stack_push(mem, adjoint_cn);

            auto primal_arg = primal(cn_call->arg());
            auto primal_arg2 =
                world_.insert(primal_arg, u64(0), mem2, primal_arg->dbg());

            auto primal_app =
                world_.app(primal_cn, primal_arg2, cn_call->dbg());
            src2primal_[cn_call] = primal_app;

            auto primal_lam = world_.nom_lam(lam->type()->as<Pi>(), lam->dbg());
            src2primal_[lam] = primal_lam;
            return primal_lam;
        } else {
            // TODO: Function calls
            THORIN_UNREACHABLE;
        }
    }

    if (auto tuple = src->isa<Tuple>()) {
        Array<const Def *> primal_ops(tuple->num_ops(), [this, tuple](auto i) {
            return primal(tuple->op(i));
        });
        auto primal_tuple = world_.tuple(primal_ops, tuple->dbg());
        src2primal_[tuple] = primal_tuple;
        return primal_tuple;
    }

    if (auto pack = src->isa<Pack>()) {
        auto primal_arity = primal(pack->arity());
        auto primal_body = primal(pack->body());
        auto primal_pack = world_.pack(primal_arity, primal_body, pack->dbg());
        src2primal_[pack] = primal_pack;
        return primal_pack;
    }

    if (auto extract = src->isa<Extract>()) {
        auto primal_tuple = primal(extract->tuple());
        auto primal_index = primal(extract->index());
        auto primal_extract =
            world_.extract(primal_tuple, primal_index, extract->dbg());
        src2primal_[extract] = primal_extract;
        return primal_extract;
    }

    if (auto insert = src->isa<Insert>()) {
        auto primal_tuple = primal(insert->tuple());
        auto primal_index = primal(insert->index());
        auto primal_value = primal(insert->value());
        auto primal_insert = world_.insert(primal_tuple, primal_index,
                                           primal_value, insert->dbg());
        src2primal_[insert] = primal_insert;
        return primal_insert;
    }

    if (auto axiom = src->isa<Axiom>()) {
        if (axiom->tag() == Tag::ROp) {
            auto primal_rop = J_wrap_ROp(ROp(axiom->flags()));
            src2primal_[axiom] = primal_rop;
            return primal_rop;
        }
    }

    // Stuff like literals, types, etc. are not interesting for AD.
    return src;
}

} // namespace

////////////////////////////////////////////////////////////////////////////////
// Public back_diff interface
////////////////////////////////////////////////////////////////////////////////

const Def *BackDiff::rewrite(const Def *def) {
    if (auto app = isa_backdiff_app(def)) {
        auto src = app->fn;
        auto dst =
            world().nom_lam(def->type()->as<Pi>(),
                            world().dbg("back_diff_" + src->debug().name));

        return BackDiffImpl(world(), src, dst).rewrite();
    }
}

} // namespace thorin
