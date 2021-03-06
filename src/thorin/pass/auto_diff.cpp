#include "auto_diff.h"

#include "../analyses/scope.h"
#include <algorithm>
#include <string>

namespace thorin {

namespace {

class AutoDiffCtx {
public:
    AutoDiffCtx(World& world, Def2Def old2new)
        : world_{world}
        , old2new_{old2new} {}

    const Def* emit_primal(const Def* def);
    const Def* emit_adjoint(const Def* def);

private:
    const Def* emit_rop_primal(const Axiom* axiom);

    World& world_;
    Def2Def old2new_;
    Def2Def app2pb_;
    Def2Def ds_grads_;
};

const Def* AutoDiffCtx::emit_primal(const Def* def) {
    if (old2new_.contains(def)) {
        return old2new_[def];
    }

    if (auto lit = def->isa<Lit>()) {
        old2new_[lit] = lit;
        return lit;
    }

    if (auto nat = def->isa<Nat>()) {
        old2new_[nat] = nat;
        return nat;
    }

    if (auto tuple = def->isa<Tuple>()) {
        Array<const Def*> new_ops{tuple->num_ops(), [&](auto i) { return emit_primal(proj(tuple, i)); }};
        auto new_tuple = world_.tuple(new_ops, tuple->debug());
        old2new_[tuple] = new_tuple;
        return new_tuple;
    }

    if (auto pack = def->isa<Pack>()) {
        auto new_body = emit_primal(pack->body());
        auto new_pack = world_.pack(pack->arity(), new_body, pack->debug());
        old2new_[pack] = new_pack;
        return new_pack;
    }

    if (auto extract = def->isa<Extract>()) {
        auto new_tuple = emit_primal(extract->tuple());
        auto new_index = emit_primal(extract->index());
        auto new_extract = world_.extract(new_tuple, new_index, extract->debug());
        old2new_[extract] = new_extract;
        return new_extract;
    }

    if (auto insert = def->isa<Insert>()) {
        auto new_tuple = emit_primal(insert->tuple());
        auto new_index = emit_primal(insert->index());
        auto new_value = emit_primal(insert->value());
        auto new_insert = world_.insert(new_tuple, new_index, new_value, insert->debug());
        old2new_[insert] = new_insert;
        return new_insert;
    }

    if (auto axiom = def->isa<Axiom>()) {
        switch (axiom->tag()) {
            case Tag::Alloc:
            case Tag::Slot:
            case Tag::Load:
            case Tag::Store: {
                errf("Memory operations are not supported for gradients: {}", def);
                std::exit(1);
            }
            case Tag::ROp: {
                return emit_rop_primal(axiom);
            }
            default: {
                return axiom;
            }
        }
    }

    if (auto lam = def->isa<Lam>()) {
        auto pi = lam->type();

        if (pi->is_returning()) {
            return world_.op_rev_diff(lam);
        }

        assert(pi->is_cn());

        auto new_body = emit_primal(lam->body());
        auto new_lam = world_.lam(pi, {"primal_" + lam->name()});
        new_lam->set_filter(lam->filter());
        new_lam->set_body(new_body);

        old2new_[lam] = new_lam;
        return new_lam;
    }

    if (auto app = def->isa<App>()) {
        auto callee = app->callee();
        auto arg = app->arg();

        auto new_callee = emit_primal(callee);

        if (new_callee->type() == callee->type()) {
            auto new_arg = emit_primal(arg);
            auto new_app = world_.app(new_callee, new_arg, app->debug());
            old2new_[app] = new_app;
            return new_app;
        }

        if (!new_callee->type()->as<Pi>()->is_cn()) {
            auto new_arg = emit_primal(arg);
            auto new_app = world_.app(new_callee, new_arg, app->debug());

            if (new_app->type()->isa<Sigma>() || new_app->type()->isa<Arr>()) {
                old2new_[app] = new_app;
                app2pb_[new_app] = proj(new_app, 2, 1);
                return proj(new_app, 2, 0);
            }

            old2new_[app] = new_app;
            return new_app;
        }

        auto cont = arg->ops().back();
        auto new_cn = new_callee->type()->as<Pi>()->domains().back()->as<Pi>();
        auto new_cont = world_.lam(new_cn, {"primal_cont"});

        auto new_cont_args = new_cont->params().skip_back();
        new_cont->set_filter(world_.lit_true());
        new_cont->set_body(world_.app(cont, new_cont_args));

        auto num_args = arg->num_ops();
        Array<const Def*> new_args{
            num_args, [&](auto i) { return i < num_args - 1 ? emit_primal(arg->op(i)) : new_cont; }};
        auto new_app = world_.app(new_callee, new_args, app->debug());

        old2new_[app] = new_app;
        app2pb_[new_app] = new_cont->params().back();
        return new_app;
    }

    if (auto param = def->isa<Param>()) {
        errf("Parameter is out of scope for gradient generation: {}", param);
        std::exit(1);
    }

    if (auto top = def->isa<Top>()) {
        return top;
    }

    if (auto bot = def->isa<Bot>()) {
        return bot;
    }

    if (auto pi = def->isa<Pi>()) {
        auto new_domain = emit_primal(pi->domain());
        auto new_codomain = emit_primal(pi->codomain());
        auto new_pi = world_.pi(new_domain, new_codomain, pi->debug());
        old2new_[pi] = new_pi;
        return new_pi;
    }

    if (auto sigma = def->isa<Sigma>()) {
        Array<const Def*> new_ops{sigma->num_ops(), [&](auto i) { return emit_primal(sigma->op(i)); }};
        auto new_sigma = world_.sigma(new_ops, sigma->debug());
        old2new_[sigma] = new_sigma;
        return new_sigma;
    }

    if (auto arr = def->isa<Arr>()) {
        auto new_domain = emit_primal(arr->domain());
        auto new_codomain = emit_primal(arr->codomain());
        auto new_arr = world_.arr(new_domain, new_codomain, arr->debug());
        old2new_[arr] = new_arr;
        return new_arr;
    }

    errf("Unknown def for gradient generation: {}", def);
    std::exit(1);
}

const Def* AutoDiffCtx::emit_rop_primal(const Axiom* axiom) {
    THORIN_BREAK;
    auto op = ROp(axiom->flags());

    auto type = world_.pi(world_.kind_star())->set_domain({world_.type_nat(), world_.type_nat()});
    auto m = type->param(0, {"m"});
    auto w = type->param(1, {"w"});
    auto real_w = world_.type_real(w);
    auto pb_pi = world_.pi(real_w, world_.sigma({real_w, real_w}));
    auto op_pi = world_.pi(world_.sigma({real_w, real_w}), world_.sigma({real_w, pb_pi}));
    type->set_codomain(op_pi);

    auto pb_lam = world_.lam(pb_pi, {"pullback_" + axiom->name()});
    auto op_lam = world_.lam(op_pi, {"primal_" + axiom->name()});
    auto axiom_lam = world_.lam(type, axiom->debug());

    axiom_lam->set_filter(world_.lit_true());
    axiom_lam->set_body(op_lam);

    auto [a, b] = op_lam->param()->split<2>();
    op_lam->set_filter(world_.lit_true());
    op_lam->set_body(world_.tuple({world_.op(op, m, a, b), pb_lam}));

    auto grad = pb_lam->param({"grad_" + axiom->name()});
    pb_lam->set_filter(world_.lit_true());

    switch (op) {
        // ∇(a + b) = λ∂f.[∂f, ∂f]
        case ROp::add: {
            pb_lam->set_body(world_.tuple({grad, grad}));
            break;
        }
        // ∇(a - b) = λ∂f.[∂f, -∂f]
        case ROp::sub: {
            pb_lam->set_body(world_.tuple({grad, world_.op_ROp_minus(m, grad)}));
            break;
        }
        // ∇(a * b) = λ∂f.[∂f*b, ∂f*a]
        case ROp::mul: {
            auto d1 = world_.op(ROp::mul, m, grad, b);
            auto d2 = world_.op(ROp::mul, m, grad, a);
            pb_lam->set_body(world_.tuple({d1, d2}));
            break;
        }
        // ∇(a / b) = λ∂f.[∂f/b, (-∂f*a)/(b²)]
        case ROp::div: {
            auto neg_grad = world_.op_ROp_minus(m, grad);
            auto d1 = world_.op(ROp::div, m, grad, b);
            auto numerator = world_.op(ROp::mul, m, neg_grad, a);
            auto denominator = world_.op(ROp::mul, m, b, b);
            auto d2 = world_.op(ROp::div, m, numerator, denominator);
            pb_lam->set_body(world_.tuple({d1, d2}));
            break;
        }
        case ROp::mod: {
            errf("Mod is not supported for gradients: {}", axiom);
            std::exit(1);
        }
    }

    return axiom_lam;
}

class AutoDiffer {
public:
    AutoDiffer(World& world, const Def* gradient, const Def2Def src_to_dst)
        : world_{world}
        , gradient_{gradient}
        , src_to_dst_{src_to_dst} {}

    const Def* reverse_diff(const Def* src);
    const Def* forward_diff(const Def*) { throw "not implemented"; }

    const Def* grad(const Def* def);

private:
    const Def* j_wrap(const Def* def);
    const Def* j_wrap_rop(ROp op, const Def* a, const Def* b);

    void fill_grad(const Def* def, const Def* cur_grad);

    const Def* seen(const Def* src);
    const Def* add_part_grad(const Def* primal_def, const Def* part_grad);

    World& world_;
    const Def* gradient_;
    Def2Def src_to_dst_;
    Def2Def dst_to_pullback_;
    Def2Def dst_to_part_diff_;
};

const Def* AutoDiffer::reverse_diff(const Def* src) {
    auto dst = j_wrap(src);
    fill_grad(dst, gradient_);
    return dst;
}

const Def* AutoDiffer::j_wrap(const Def* def) {
    if (auto dst = seen(def))
        return dst;

    if (auto param = def->isa<Param>()) {
        errf("This param must be out of scope: {}\n This is not differentiable", param);
        THORIN_UNREACHABLE;
    }

    if (auto axiom = def->isa<Axiom>()) {
        errf("Found a non-differentiable axiom: {}", axiom);
        THORIN_UNREACHABLE;
    }

    if (auto lam = def->isa_nominal<Lam>()) {
        auto dst = world_.lam(lam->type(), {lam->name()});
        src_to_dst_[lam->param()] = dst->param();
        dst->set_filter(lam->filter());
        dst->set_body(j_wrap(lam->body()));
        src_to_dst_[lam] = dst;
        return dst;
    }

    if (auto app = def->isa<App>()) {
        auto callee = app->callee();
        auto arg = app->arg();

        if (auto inner = callee->isa<App>()) {
            if (auto axiom = inner->callee()->isa<Axiom>()) {
                if (axiom->tag() == Tag::ROp) {
                    auto [a, b] = j_wrap(arg)->split<2>();
                    auto [dst, pb] = j_wrap_rop(ROp(axiom->flags()), a, b)->split<2>();
                    dst_to_pullback_[dst] = pb;
                    src_to_dst_[app] = dst;
                    return dst;
                }

                if (axiom->tag() == Tag::RCmp) {
                    auto [a, b] = j_wrap(arg)->split<2>();
                    auto dst = world_.op(RCmp(axiom->flags()), nat_t(0), a, b);
                    src_to_dst_[app] = dst;
                    return dst;
                }
            }
        }

        if (callee->type()->as<Pi>()->is_returning()) {
            auto rd_callee = world_.op_rev_diff(callee);

            auto wrapper_pi = rd_callee->type()->as<Pi>()->domains().back()->as<Pi>();
            auto wrapper_lam = world_.lam(wrapper_pi, {"wrapper"});

            wrapper_lam->set_filter(world_.lit_true());
            wrapper_lam->set_body(world_.app(j_wrap(app->args().back()), wrapper_lam->params().skip_back()));

            auto num_args = app->num_args();
            Array<const Def*> args{
                num_args, [&](auto i) { return i < num_args - 1 ? j_wrap(app->arg(i)) : wrapper_lam; }};

            auto dst = world_.app(rd_callee, args);
            dst_to_pullback_[dst] = wrapper_lam->params().back();
            src_to_dst_[app] = dst;
            return dst;
        }

        auto dst = world_.app(j_wrap(callee), j_wrap(arg));
        src_to_dst_[app] = dst;
        return dst;
    }

    if (auto tuple = def->isa<Tuple>()) {
        Array<const Def*> ops{tuple->num_ops(), [&](auto i) { return j_wrap(tuple->op(i)); }};
        auto dst = world_.tuple(ops);
        src_to_dst_[tuple] = dst;
        return dst;
    }

    if (auto pack = def->isa<Pack>()) {
        auto dst = world_.pack(pack->type()->arity(), j_wrap(pack->body()));
        src_to_dst_[pack] = dst;
        return dst;
    }

    if (auto extract = def->isa<Extract>()) {
        auto dst = world_.extract(j_wrap(extract->tuple()), j_wrap(extract->index()));
        src_to_dst_[extract] = dst;
        return dst;
    }

    if (auto insert = def->isa<Insert>()) {
        auto dst = world_.insert(j_wrap(insert->tuple()), j_wrap(insert->index()), j_wrap(insert->value()));
        src_to_dst_[insert] = dst;
        return dst;
    }

    if (auto lit = def->isa<Lit>()) {
        return lit;
    }

    errf("I don't know yet how to handle: {}", def);
    THORIN_UNREACHABLE;
}

const Def* AutoDiffer::j_wrap_rop(ROp op, const Def* a, const Def* b) {
    auto r_type = a->type();
    auto pi = world_.pi(r_type, world_.sigma({r_type, r_type}));

    switch (op) {
        // ∇(a + b) = λ∂f.[∂f, ∂f]
        case ROp::add: {
            auto B = world_.lam(pi, {"φ+"});
            auto param = B->param();
            B->set_filter(world_.lit_true());
            B->set_body(world_.tuple({param, param}));
            return world_.tuple({world_.op(ROp::add, (nat_t)0, a, b), B});
        }
        // ∇(a - b) = λ∂f.[∂f, -∂f]
        case ROp::sub: {
            auto B = world_.lam(pi, {"φ-"});
            auto param = B->param();
            B->set_filter(world_.lit_true());
            B->set_body(world_.tuple({param, world_.op_ROp_minus((nat_t)0, param)}));
            return world_.tuple({world_.op(ROp::sub, (nat_t)0, a, b), B});
        }
        // ∇(a * b) = λ∂f.[∂f*b, ∂f*a]
        case ROp::mul: {
            auto B = world_.lam(pi, {"φ*"});
            auto param = B->param();
            auto d1 = world_.op(ROp::mul, nat_t(0), param, b);
            auto d2 = world_.op(ROp::mul, nat_t(0), param, a);
            B->set_filter(world_.lit_true());
            B->set_body(world_.tuple({d1, d2}));
            return world_.tuple({world_.op(ROp::mul, (nat_t)0, a, b), B});
        }
        // ∇(a / b) = λ∂f.[∂f/b, (-∂f*a)/(b²)]
        case ROp::div: {
            auto B = world_.lam(pi, {"φ/"});
            auto param = B->param();
            auto neg_param = world_.op_ROp_minus(nat_t(0), B->param());
            auto d1 = world_.op(ROp::div, nat_t(0), param, b);
            auto numerator = world_.op(ROp::mul, nat_t(0), neg_param, a);
            auto denominator = world_.op(ROp::mul, nat_t(0), b, b);
            auto d2 = world_.op(ROp::div, nat_t(0), numerator, denominator);
            B->set_filter(world_.lit_true());
            B->set_body(world_.tuple({d1, d2}));
            return world_.tuple({world_.op(ROp::div, (nat_t)0, a, b), B});
        }
        case ROp::mod: return nullptr;
    }
}

void AutoDiffer::fill_grad(const Def* def, const Def* cur_grad) {
    if (auto lam = def->isa_nominal<Lam>()) {
    }

    if (auto app = def->isa<App>()) {
        if (dst_to_pullback_.contains(app)) {
            auto pb = dst_to_pullback_[app];

            if (pb->type()->as<Pi>()->is_cn()) {
                /*
                auto lam = world_.lam(pb->type()->as<Pi>(), {"adjoint_cn"});
                auto grads = lam->params().skip_back().skip_back();
                for (size_t i = 0; i < app->num_args(); ++i) {
                    fill_grad(app->arg(i), grads[i]);
                }
                */

                THORIN_BREAK;
            } else {
                auto grads = world_.app(pb, cur_grad, {"∇" + app->callee()->name()});
                for (size_t i = 0; i < app->num_args(); ++i) {
                    fill_grad(app->arg(i), world_.extract(grads, i, {"∇" + std::to_string(i)}));
                }
            }
        } else {
            for (size_t i = 0; i < app->num_args(); ++i) {
                fill_grad(app->arg(i), cur_grad);
            }
        }
    }

    if (auto tuple = def->isa<Tuple>()) {
        for (auto op : tuple->ops()) {
            fill_grad(op, cur_grad);
        }
    }

    if (auto pack = def->isa<Pack>()) {
        fill_grad(pack->body(), cur_grad);
    }

    if (auto extract = def->isa<Extract>()) {
        if (auto param = extract->tuple()->isa<Param>()) {
            add_part_grad(extract, cur_grad);
        } else {
            fill_grad(extract->tuple(), cur_grad);
        }
    }

    if (auto insert = def->isa<Insert>()) {
        errf("Insert is not supported");
        THORIN_UNREACHABLE;
    }
}

const Def* AutoDiffer::grad(const Def* def) {
    if (!dst_to_part_diff_.contains(def)) {
        return world_.lit_real(r64(0));
    }
    return dst_to_part_diff_[def];
}

const Def* AutoDiffer::add_part_grad(const Def* primal_def, const Def* part_grad) {
    if (!dst_to_part_diff_.contains(primal_def)) {
        dst_to_part_diff_[primal_def] = part_grad;
        return part_grad;
    }

    auto old_part_grad = dst_to_part_diff_[primal_def];
    auto new_part_grad = world_.op(ROp::add, nat_t(0), old_part_grad, part_grad, {"∂" + part_grad->name()});
    dst_to_part_diff_[primal_def] = new_part_grad;

    return new_part_grad;
}

const Def* AutoDiffer::seen(const Def* def) { return src_to_dst_.contains(def) ? src_to_dst_[def] : nullptr; }

} // namespace

const Def* AutoDiff::rewrite(const Def* def) {
    if (auto app = def->isa<App>()) {
        if (auto type_app = app->callee()->isa<App>()) {
            if (auto axiom = type_app->callee()->isa<Axiom>(); axiom && axiom->tag() == Tag::RevDiff) {
                auto src_lam = app->arg(0)->as_nominal<Lam>();
                auto src_pi = src_lam->type()->as<Pi>();
                auto& world = src_lam->world();

                auto dst_pi = app->type()->as<Pi>();
                auto dst_lam = world.lam(dst_pi, {"rev_diff_" + src_lam->name()});

                auto pb_pi = dst_pi->domains().back()->as<Pi>();
                auto pb_lam = world.lam(pb_pi, {"pullback_" + src_lam->name()});
                auto [pb_mem, pb_grad, pb_ret] = pb_lam->param()->split<3>();

                auto ret_pi = src_pi->domains().back()->as<Pi>();
                auto ret_lam = world.lam(ret_pi, {"wrapper"});

                Def2Def src_to_dst;
                for (size_t i = 0, e = src_lam->num_params(); i < e; ++i) {
                    auto src_param = src_lam->param(i);
                    auto dst_param = dst_lam->param(i, {src_param->name()});
                    src_to_dst[src_param] = i == e - 1 ? ret_lam : dst_param;
                }

                THORIN_BREAK;
                auto ctx = AutoDiffCtx{world, src_to_dst};
                auto primal = ctx.emit_primal(src_lam->body());
                dst_lam->set_filter(src_lam->filter());
                dst_lam->set_body(primal);
                scope(dst_lam);
                THORIN_BREAK;

                auto differ = AutoDiffer{world, pb_grad, src_to_dst};

                dst_lam->set_filter(src_lam->filter());
                dst_lam->set_body(differ.reverse_diff(src_lam->body()));

                auto num_ret_body_args = dst_pi->domains().back()->as<Pi>()->num_domains();
                Array<const Def*> ret_body_args{num_ret_body_args,
                    [&](auto i) { return i < num_ret_body_args - 1 ? ret_lam->param(i) : pb_lam; }};
                ret_lam->set_filter(world.lit_true());
                ret_lam->set_body(world.app(dst_lam->ret_param({"return"}), ret_body_args));

                auto num_grads = src_lam->num_params() - 2;
                Array<const Def*> grads{num_grads, [&](auto i) { return differ.grad(dst_lam->param(i + 1)); }};
                pb_lam->set_filter(world.lit_true());
                pb_lam->set_body(world.app(pb_lam->ret_param(), {pb_lam->mem_param(), world.tuple(grads)}));

                THORIN_BREAK;
                return dst_lam;
            }
        }
    }

    return def;
}

} // namespace thorin
