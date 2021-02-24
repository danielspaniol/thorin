#include "backdiff.h"
#include "thorin/analyses/scope.h"

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
    const Pi *primal_type(Lam *lam);
    const Pi *pullback_type(Lam *lam);
    const Pi *adjoint_type(Lam *lam);

    const Pi *back_type(const Pi *pi);
    const Pi *primal_type(const Pi *pi);
    const Pi *pullback_type(const Pi *pi, const Pi *next_pi);
    const Pi *adjoint_type(const Pi *pi, const Pi *next_pi);

    // ========== Continuations

    Lam *primal(Lam *orig);
    Lam *pullback(Lam *orig, Lam *primal);
    Lam *adjoint(Lam *orig, Lam *primal);

    const Def *back_var(Lam *orig, Lam *primal);
    const Def *final_ret_var(Lam *adjoint);

    // ========== J Wrapper

    const Def *J(const Def *def, const Scope &scope);

    // ========== Partial Tangents

    DefArr collect_local_tangents(Lam *primal);
    const Def *update_global_tangents(const Def *mem,
                                      const DefArr &local_tangents);

    // ========== Debug

    const Def *primal_name(const Def *def);
    const Def *adjoint_name(const Def *def);
    const Def *pullback_name(const Def *def);
    const Def *back_name(const Def *def);
    const Def *add_to_name(const Def *def, const std::string &str);

    // ========== Helpers

    const Def *add_back(const Def *target, const Def *def);

  private:
    World &world_;
    Lam *src_;
    const Pi *final_ret_type_;
    Def2Def old2new_;
};

Algo::Algo(World &world, Lam *lam)
    : world_{world}, src_{lam}, final_ret_type_{nullptr} {}

Lam *Algo::rewrite() {
    (void)primal(src_);
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

    return world_.sigma();
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
    return world_.cn(back_ops, back_name(pi));
}

const Pi *Algo::primal_type(const Pi *pi) {
    auto ops = pi->dom()->ops();
    auto back_pi = back_type(pi);
    DefArr primal_ops{ops.size() + 1, [&ops, back_pi](auto i) {
                          return i < ops.size() ? ops[i] : back_pi;
                      }};
    return world_.cn(primal_ops, primal_name(pi));
}

const Pi *Algo::pullback_type(const Pi *pi, const Pi *next_pi) {
    auto ops = next_pi->dom()->ops();
    DefArr pullback_ops{ops.size() + 1, [this, &ops](auto i) {
                            return i < ops.size() ? tangent_type(ops[i])
                                                  : final_ret_type();
                        }};
    return world_.cn(pullback_ops, pullback_name(pi));
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
    return world_.cn(adjoint_ops, adjoint_name(pi));
}

// ========== Continuations

Lam *Algo::primal(Lam *orig) {
    if (auto primal_lam = old2new_.lookup(orig)) {
        return (*primal_lam)->as_nom<Lam>();
    }

    Scope scope{orig};

    auto primal_pi = primal_type(orig);
    auto primal_lam = world_.nom_lam(primal_pi, primal_name(orig));

    old2new_[orig] = primal_lam;

    auto app = orig->body()->as<App>();
    auto next = app->callee();
    auto arg = app->arg();

    auto primal_arg = add_back(J(arg, scope), pullback(orig, primal_lam));
    auto primal_next = J(next, scope);
    auto primal_app = world_.app(primal_arg, primal_next, app->dbg());

    primal_lam->set_body(primal_app);
    primal_lam->set_filter(orig->filter());

    return primal_lam;
}

Lam *Algo::pullback(Lam *orig, Lam *primal) {
    auto pullback_pi = pullback_type(orig);
    auto pullback_lam = world_.nom_lam(pullback_pi, pullback_name(orig));

    auto var = primal->var();
    auto arg = add_back(var, back_var(orig, primal));
    auto app = world_.app(adjoint(orig, primal), arg);

    pullback_lam->set_body(app);
    pullback_lam->set_filter(true);

    return pullback_lam;
}

Lam *Algo::adjoint(Lam *orig, Lam *primal) {
    auto adjoint_pi = adjoint_type(orig);
    auto adjoint_lam = world_.nom_lam(adjoint_pi, adjoint_name(orig));

    auto back = back_var(orig, adjoint_lam);
    auto final_ret = final_ret_var(adjoint_lam);
    auto mem = adjoint_lam->mem_var();

    auto tangents = collect_local_tangents(primal);
    auto mem2 = update_global_tangents(mem, tangents);

    DefArr arg_ops{tangents.size() + 2, [mem2, final_ret, &tangents](auto i) {
                       if (i == 0)
                           return mem2;
                       if (i == tangents.size() + 1)
                           return final_ret;
                       return tangents[i];
                   }};
    auto app = world_.app(back, arg_ops);

    adjoint_lam->set_body(app);
    adjoint_lam->set_filter(true);

    return adjoint_lam;
}

const Def *Algo::back_var(Lam *orig, Lam *primal) {
    return primal->var(primal->num_vars() - 1, back_name(orig));
}

const Def *Algo::final_ret_var(Lam *adjoint) {
    return adjoint->var(adjoint->num_vars() - 2, world_.dbg("final_ret"));
}

// ========== J Wrapper

const Def *Algo::J(const Def *def, const Scope &scope) {
    (void)scope;
    return def; // TODO
}

// ========== Partial Tangents

DefArr Algo::collect_local_tangents(Lam *primal) {
    (void)primal;
    return {}; // TODO
}

const Def *Algo::update_global_tangents(const Def *mem,
                                        const DefArr &local_tangents) {
    (void)local_tangents;
    return mem; // TODO
}

// ========== Debug

const Def *Algo::primal_name(const Def *def) {
    return add_to_name(def, "_primal");
}

const Def *Algo::adjoint_name(const Def *def) {
    return add_to_name(def, "_adjoint");
}

const Def *Algo::pullback_name(const Def *def) {
    return add_to_name(def, "_pullback");
}

const Def *Algo::back_name(const Def *def) { return add_to_name(def, "_back"); }

const Def *Algo::add_to_name(const Def *def, const std::string &str) {
    return world_.dbg(def->debug().name + str);
}

// ========== Helpers

const Def *Algo::add_back(const Def *target, const Def *def) {
    if (auto tuple = target->isa<Tuple>()) {
        auto ops = tuple->ops();
        DefArr new_ops{ops.size() + 1, [&ops, def](auto i) {
                           return i < ops.size() ? ops[i] : def;
                       }};
        return world_.tuple(ops);
    }
    return world_.tuple({target, def});
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
