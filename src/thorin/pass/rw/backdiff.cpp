#include "backdiff.h"

namespace thorin {

////////////////////////////////////////////////////////////////////////////////
// IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////

namespace {

using DefArr = Array<const Def *>;

class Algo {
  public:
    Algo(World &world, Lam *lam);

    Lam *rewrite();

  private:
    // ========== Vector Space

    const Def *tangent_type(const Def *type);

    // ========== Types

    const Pi *final_ret_type();
    const Pi *back_type(Lam *lam);
    const Pi *primal_type(Lam *lam);
    const Pi *pullback_type(Lam *lam);
    const Pi *adjoint_type(Lam *lam);

    const Pi *back_type(const Pi *pi);
    const Pi *primal_type(const Pi *pi);
    const Pi *pullback_type(const Pi *pi, const Pi *next_pi);
    const Pi *adjoint_type(const Pi *pi, const Pi *next_pi);

  private:
    World &world_;
    Lam *src_;
    const Pi *final_ret_type_;
};

Algo::Algo(World &world, Lam *lam)
    : world_{world}, src_{lam}, final_ret_type_{nullptr} {}

Lam *Algo::rewrite() {
    return nullptr; // TODO
}

// ========== Vector Space

const Def *Algo::tangent_type(const Def *type) {
    if (isa<Tag::Real>(type)) {
        return type;
    }

    if (isa<Tag::Mem>(type)) {
        return type;
    }

    if (auto sigma = type->isa<Sigma>()) {
        auto ops = sigma->ops();
        DefArr tangent_ops{
            ops.size(), [this, &ops](auto i) { return tangent_type(ops[i]); }};
        return world_.sigma(tangent_ops, sigma->dbg());
    }

    if (auto pi = type->isa<Pi>(); pi && pi->is_cn()) {
        return primal_type(pi);
    }
}

// ========== Types

const Pi *Algo::final_ret_type() {
    if (!final_ret_type_) {
        auto dom = src_->dom();
        auto ops = dom->ops().skip_back();
        DefArr final_ret_ops{
            ops.size(), [this, &ops](auto i) { return tangent_type(ops[i]); }};
        final_ret_type_ = world_.cn(final_ret_ops, world_.dbg("FinalRetT"));
    }

    return final_ret_type_;
}

const Pi *Algo::back_type(Lam *lam) { return back_type(lam->type()); }

const Pi *Algo::primal_type(Lam *lam) { return primal_type(lam->type()); }

const Pi *Algo::pullback_type(Lam *lam) {
    return pullback_type(lam->type(),
                         lam->body()->as<App>()->callee()->type()->as<Pi>());
}

const Pi *Algo::adjoint_type(Lam *lam) {
    return adjoint_type(lam->type(),
                        lam->body()->as<App>()->callee()->type()->as<Pi>());
}

const Pi *Algo::back_type(const Pi *pi) {
    auto ops = pi->dom()->ops();
    DefArr back_ops{ops.size() + 1, [this, &ops](auto i) {
                        return i < ops.size() ? tangent_type(ops[i])
                                              : final_ret_type();
                    }};
    return world_.cn(back_ops, world_.dbg(pi->debug().name + "_back"));
}

const Pi *Algo::primal_type(const Pi *pi) {
    auto ops = pi->dom()->ops();
    auto back_pi = back_type(pi);
    DefArr primal_ops{ops.size() + 1, [&ops, back_pi](auto i) {
                          return i < ops.size() ? ops[i] : back_pi;
                      }};
    return world_.cn(primal_ops, world_.dbg(pi->debug().name + "_primal"));
}

const Pi *Algo::pullback_type(const Pi *pi, const Pi *next_pi) {
    auto ops = next_pi->dom()->ops();
    DefArr pullback_ops{ops.size() + 1, [this, &ops](auto i) {
                            return i < ops.size() ? tangent_type(ops[i])
                                                  : final_ret_type();
                        }};
    return world_.cn(pullback_ops, world_.dbg(pi->debug().name + "_pullback"));
}

const Pi *Algo::adjoint_type(const Pi *pi, const Pi *next_pi) {
    auto ops = next_pi->dom()->ops();
    DefArr adjoint_ops{ops.size() + 2, [this, &ops, pi](auto i) -> const Def * {
                           if (i < ops.size())
                               return tangent_type(ops[i]);
                           if (i < ops.size() + 1)
                               return final_ret_type();
                           return back_type(pi);
                       }};
    return world_.cn(adjoint_ops, world_.dbg(pi->debug().name + "_adjoint"));
}

} // namespace

////////////////////////////////////////////////////////////////////////////////
// PUBLIC INTERFACE
////////////////////////////////////////////////////////////////////////////////

Lam *isa_lam_for_backdiff(const Def *) {
    return nullptr; // TODO
}

const Def *BackDiff::rewrite(const Def *def) {
    if (auto lam = isa_lam_for_backdiff(def)) {
        return Algo{world(), lam}.rewrite();
    }
    return def;
}

} // namespace thorin
