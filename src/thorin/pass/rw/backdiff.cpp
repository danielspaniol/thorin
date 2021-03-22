#include "backdiff.h"
#include "thorin/analyses/scope.h"
#include "thorin/axiom.h"
#include "thorin/def.h"
#include "thorin/lam.h"
#include "thorin/util/utility.h"

#include <vector>

namespace thorin {

using DefArr = Array<const Def *>;
using DefDefArr = std::vector<DefDef>;

////////////////////////////////////////////////////////////////////////////////
// NAMING
////////////////////////////////////////////////////////////////////////////////

const Def *BackDiffNaming::primal(const Def *def) {
  return add_to_name(def, "_primal");
}

const Def *BackDiffNaming::adjoint(const Def *def) {
  return add_to_name(def, "_adjoint");
}

const Def *BackDiffNaming::pullback(const Def *def) {
  return add_to_name(def, "_pullback");
}

const Def *BackDiffNaming::back(const Def *def) {
  return add_to_name(def, "_back");
}

const Def *BackDiffNaming::tangent_init(const Def *def) {
  return add_to_name(def, "_tangent_init");
}

const Def *BackDiffNaming::add_to_name(const Def *def, const std::string &str) {
  return world_.dbg(def->debug().name + str);
}

////////////////////////////////////////////////////////////////////////////////
// TYPING
////////////////////////////////////////////////////////////////////////////////

const Def *BackDiffTyping::tangent(const Def *type) {
  if (isa<Tag::Real>(type)) {
    return type;
  }

  if (isa<Tag::Mem>(type)) {
    return type;
  }

  if (auto sigma = type->isa<Sigma>()) {
    auto ops = sigma->ops();
    DefArr tangent_ops{ops.size(),
                       [this, &ops](auto i) { return tangent(ops[i]); }};
    return world_.sigma(tangent_ops, sigma->dbg());
  }

  if (auto pi = type->isa<Pi>(); pi && pi->is_cn()) {
    return primal(pi);
  }

  return world_.sigma();
}

const Pi *BackDiffTyping::final_ret() {
  if (!final_ret_) {
    auto dom = src_->dom();
    auto ops = dom->ops().skip_back();
    DefArr final_ret_ops{ops.size(),
                         [this, &ops](auto i) { return tangent(ops[i]); }};
    final_ret_ = world_.cn(final_ret_ops, world_.dbg("FinalRetT"));
  }

  return final_ret_;
}

const Pi *BackDiffTyping::primal(Lam *lam) { return primal(lam->type()); }

const Pi *BackDiffTyping::pullback(Lam *lam) {
  return pullback(lam->type(),
                  lam->body()->as<App>()->callee()->type()->as<Pi>());
}

const Pi *BackDiffTyping::adjoint(Lam *lam) {
  return adjoint(lam->type(),
                 lam->body()->as<App>()->callee()->type()->as<Pi>());
}

const Pi *BackDiffTyping::back(const Pi *pi) {
  auto ops = pi->dom()->ops();
  DefArr back_ops{ops.size() + 1, [this, &ops](auto i) {
                    return i < ops.size() ? tangent(ops[i]) : final_ret();
                  }};
  return world_.cn(back_ops, naming_.back(pi));
}

const Pi *BackDiffTyping::primal(const Pi *pi) {
  auto ops = pi->dom()->ops();
  auto back_pi = back(pi);
  DefArr primal_ops{ops.size() + 1, [&ops, back_pi](auto i) {
                      return i < ops.size() ? ops[i] : back_pi;
                    }};
  return world_.cn(primal_ops, naming_.primal(pi));
}

const Pi *BackDiffTyping::pullback(const Pi *pi, const Pi *next_pi) {
  auto ops = next_pi->dom()->ops();
  DefArr pullback_ops{ops.size() + 1, [this, &ops](auto i) {
                        return i < ops.size() ? tangent(ops[i]) : final_ret();
                      }};
  return world_.cn(pullback_ops, naming_.pullback(pi));
}

const Pi *BackDiffTyping::adjoint(const Pi *pi, const Pi *next_pi) {
  auto ops = next_pi->dom()->ops();
  DefArr adjoint_ops{ops.size() + 2, [this, &ops, pi](auto i) -> const Def * {
                       if (i < ops.size())
                         return tangent(ops[i]);
                       if (i < ops.size() + 1)
                         return final_ret();
                       return back(pi);
                     }};
  return world_.cn(adjoint_ops, naming_.adjoint(pi));
}

const Pi *BackDiffTyping::tangent_init(Lam *orig_lam) {
  return primal(orig_lam->body()->as<App>()->callee()->as_nom<Lam>());
}

////////////////////////////////////////////////////////////////////////////////
// IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////

namespace {

class Algo {
public:
  Algo(World &world, Lam *lam);

  Lam *rewrite();

private:
  // ========== Continuations

  Lam *primal(Lam *orig);
  Lam *pullback(Lam *orig, Lam *primal);
  Lam *adjoint(Lam *orig, Lam *primal);

  const Def *back_var(Lam *orig, Lam *primal);
  const Def *final_ret_var(Lam *adjoint);

  void link_vars(Lam *orig, Lam *primal);

  Lam *binding_lam(const Def *free_var);

  // ========== J Wrapper

  const Def *J(const Def *def, const Scope &scope);
  const Def *J_generic(const Def *def, const Scope &scope);
  const Def *J_free(const Def *free_def, const Scope &scope);
  const Def *J_ROp(const Axiom *axiom);
  const Def *J_Load(const Def *mem, const Def *ptr);
  const Def *J_Store(const Def *mem, const Def *ptr, const Def *val);
  const Def *J_App(const App *app, const Scope &scope);
  const Def *J_Tuple(const Tuple *tuple, const Scope &scope);
  const Def *J_Pack(const Pack *pack, const Scope &scope);
  const Def *J_Insert(const Insert *insert, const Scope &scope);
  const Def *J_Extract(const Extract *extract, const Scope &scope);

  // ========== Partial Tangents

  void init_tangent_zero(Lam *primal_lam, const Def *val,
                         const Def *tangent_type);

  const Def *tangent_zero(const Def *tangent_type);
  const Def *tangent_plus(const Def *tangent_type, const Def *a, const Def *b);

  DefDefArr collect_local_tangents(Lam *primal);
  const Def *update_global_tangents(const Def *mem,
                                    const DefDefArr &local_tangents);

  // ========== Helpers

  const Def *add_back(const Def *target, const Def *def);
  const Def *replace_front(const Def *target, const Def *def);

private:
  BackDiffNaming naming_;
  BackDiffTyping typing_;
  World &world_;
  Lam *src_;
  Def2Def old2new_;
  Def2Def val2pullback_;
  Def2Def primal2mem_; //< points to the current mem object to initialize
  // mutable tangents
  Def2Def val2global_tangent_;
};

Algo::Algo(World &world, Lam *lam)
    : naming_{world}, typing_{world, lam}, world_{world}, src_{lam} {}

Lam *Algo::rewrite() {
  (void)primal(src_);
  return nullptr; // TODO
}

// ========== Continuations

Lam *Algo::primal(Lam *orig) {
  if (auto primal_lam = old2new_.lookup(orig)) {
    return (*primal_lam)->as_nom<Lam>();
  }

  Scope scope{orig};

  auto primal_pi = typing_.primal(orig);
  auto primal_lam = world_.nom_lam(primal_pi, naming_.primal(orig));

  auto tangent_init_pi = typing_.tangent_init(orig);
  auto tangent_init_lam =
      world_.nom_lam(tangent_init_pi, naming_.tangent_init(orig));

  old2new_[orig] = primal_lam;
  primal2mem_[primal_lam] = tangent_init_lam->mem_var();
  link_vars(orig, primal_lam);

  auto app = orig->body()->as<App>();
  auto next = app->callee();
  auto arg = app->arg();

  auto primal_arg = add_back(J(arg, scope), pullback(orig, primal_lam));
  auto primal_next = J(next, scope);
  auto primal_app = world_.app(tangent_init_lam, primal_arg, app->dbg());

  primal_lam->set_body(primal_app);
  primal_lam->set_filter(orig->filter());

  auto tangent_init_arg =
      replace_front(tangent_init_lam->var(), *primal2mem_[primal_lam]);
  auto tangent_init_app = world_.app(primal_next, tangent_init_arg);

  tangent_init_lam->set_body(tangent_init_app);
  tangent_init_lam->set_filter(true);

  return primal_lam;
}

Lam *Algo::pullback(Lam *orig, Lam *primal) {
  auto pullback_pi = typing_.pullback(orig);
  auto pullback_lam = world_.nom_lam(pullback_pi, naming_.pullback(orig));

  auto var = primal->var();
  auto arg = add_back(var, back_var(orig, primal));
  auto app = world_.app(adjoint(orig, primal), arg);

  pullback_lam->set_body(app);
  pullback_lam->set_filter(true);

  return pullback_lam;
}

Lam *Algo::adjoint(Lam *orig, Lam *primal) {
  auto adjoint_pi = typing_.adjoint(orig);
  auto adjoint_lam = world_.nom_lam(adjoint_pi, naming_.adjoint(orig));

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
                   return std::get<0>(tangents[i]);
                 }};
  auto app = world_.app(back, arg_ops);

  adjoint_lam->set_body(app);
  adjoint_lam->set_filter(true);

  return adjoint_lam;
}

const Def *Algo::back_var(Lam *orig, Lam *primal) {
  return primal->var(primal->num_vars() - 1, naming_.back(orig));
}

const Def *Algo::final_ret_var(Lam *adjoint) {
  return adjoint->var(adjoint->num_vars() - 2, world_.dbg("final_ret"));
}

void Algo::link_vars(Lam *orig, Lam *primal) {
  for (size_t i = 0, e = orig->num_vars(); i < e; ++i) {
    auto orig_var = orig->var(i);
    auto primal_var = primal->var(i, orig_var->dbg());
    old2new_[orig_var] = primal_var;
  }
}

Lam *Algo::binding_lam(const Def *free_var) {
  if (free_var->isa<Axiom>() || isa_lit(free_var) || free_var->isa<Global>()) {
    return nullptr;
  }

  if (auto var = free_var->isa<Var>()) {
    return var->nom()->as_nom<Lam>();
  }

  Lam *innermost = nullptr;
  std::optional<Scope> scope{};
  for (auto op : free_var->ops()) {
    if (auto lam = binding_lam(op); lam && lam != innermost) {
      if (scope->bound(lam)) {
        innermost = lam;
        scope.emplace(innermost);
      }
    }
  }

  return innermost;
}

// ========== J Wrapper

const Def *Algo::J(const Def *def, const Scope &scope) {
  if (auto wrapped = old2new_.lookup(def)) {
    return *wrapped;
  }

  if (auto lam = def->isa_nom<Lam>()) {
    return primal(lam);
  }

  if (!scope.bound(def)) {
    return J_free(def, scope);
  }

  if (auto axiom = def->as<Axiom>()) {
    if (axiom->tag() == Tag::ROp) {
      return J_ROp(axiom);
    }
  }

  if (auto app = def->isa<App>()) {

    if (auto inner_app = app->callee()->isa<App>()) {
      if (auto axiom = inner_app->callee()->isa<Axiom>()) {
        if (axiom->tag() == Tag::Load) {
          auto [mem, ptr] = J(app->arg(), scope)->split<2>();
          return J_Load(mem, ptr);
        }

        if (axiom->tag() == Tag::Store) {
          auto [mem, ptr, val] = J(app->arg(), scope)->split<3>();
          return J_Store(mem, ptr, val);
        }
      }
    }

    return J_App(app, scope);
  }

  if (auto tuple = def->isa<Tuple>()) {
    return J_Tuple(tuple, scope);
  }

  if (auto pack = def->isa<Pack>()) {
    return J_Pack(pack, scope);
  }

  if (auto insert = def->isa<Insert>()) {
    return J_Insert(insert, scope);
  }

  if (auto extract = def->isa<Extract>()) {
    return J_Extract(extract, scope);
  }

  return J_generic(def, scope);
}

const Def *Algo::J_generic(const Def *def, const Scope &scope) {
  auto ops = def->ops();
  DefArr new_ops{ops.size(),
                 [this, ops, &scope](auto i) { return J(ops[i], scope); }};
  auto new_def = def->rebuild(world_, def->type(), new_ops, def->dbg());
  old2new_[def] = new_def;
  return new_def;
}

const Def *Algo::J_free(const Def *free_def, const Scope &scope) {
  auto lam = binding_lam(free_def);
  auto primal_lam = (*old2new_[lam])->as_nom<Lam>();
  auto tangent_type = typing_.tangent(free_def->type());

  init_tangent_zero(primal_lam, free_def, tangent_type);

  return J_generic(free_def, scope);
}

const Def *Algo::J_ROp(const Axiom *axiom) {
  auto type =
      world_.nom_pi(world_.kind(), {world_.type_nat(), world_.type_nat()});
  auto m = type->var(0, world_.dbg("m"));
  auto real_w = world_.type_real(type->var(1, world_.dbg("w")));

  auto pullback_pi = world_.pi(real_w, world_.sigma({real_w, real_w}));
  auto pullback_lam = world_.nom_lam(pullback_pi, naming_.pullback(axiom));

  auto impl_pi = world_.pi(world_.tuple({real_w, real_w}), real_w);
  auto impl_lam = world_.nom_lam(impl_pi, axiom->dbg());

  type->set_codom(
      world_.pi({real_w, real_w}, world_.sigma({real_w, pullback_pi})));

  auto lam = world_.nom_lam(type, axiom->dbg());
  lam->set_body(impl_lam);
  lam->set_filter(true);

  auto op = ROp(axiom->flags());
  auto a = impl_lam->var(0, world_.dbg("a"));
  auto b = impl_lam->var(1, world_.dbg("b"));
  auto res = world_.op(op, m, a, b, world_.dbg("res"));
  impl_lam->set_body(world_.tuple({res, pullback_lam}));
  impl_lam->set_filter(true);

  auto tan = pullback_lam->var(0, world_.dbg("∂res"));
  auto neg_tan = world_.op_negate(tan, world_.dbg("-∂res"));
  pullback_lam->set_filter(true);

  switch (op) {
  case ROp::add: {
    auto tan_a = tan;
    auto tan_b = tan;
    pullback_lam->set_body(world_.tuple({tan_a, tan_b}));
    break;
  }
  case ROp::sub: {
    auto tan_a = tan;
    auto tan_b = neg_tan;
    pullback_lam->set_body(world_.tuple({tan_a, tan_b}));
    break;
  }
  case ROp::mul: {
    auto tan_a = world_.op(ROp::mul, m, b, tan, world_.dbg("∂a"));
    auto tan_b = world_.op(ROp::mul, m, a, tan, world_.dbg("∂b"));
    pullback_lam->set_body(world_.tuple({tan_a, tan_b}));
    break;
  }
  case ROp::div: {
    auto tan_a = world_.op(ROp::div, m, tan, b, world_.dbg("∂a"));
    auto tan_b = world_.op(ROp::mul, m, world_.op(ROp::mul, m, neg_tan, a),
                           world_.op(ROp::mul, m, b, b), world_.dbg("∂b"));
    pullback_lam->set_body(world_.tuple({tan_a, tan_b}));
    break;
  }
  case ROp::rem:
    return axiom;
  }

  old2new_[axiom] = lam;
  return lam;
}

const Def *Algo::J_Load(const Def *mem, const Def *ptr) {
  // TODO
  (void)ptr;
  return mem;
}

const Def *Algo::J_Store(const Def *mem, const Def *ptr, const Def *val) {
  // TODO
  (void)ptr;
  (void)val;
  return mem;
}

const Def *Algo::J_App(const App *app, const Scope &scope) {
  auto callee = app->callee();
  auto arg = app->arg();

  auto Jcallee = J(callee, scope);
  auto Jarg = J(arg, scope);
  auto Japp = world_.app(Jcallee, Jarg, app->dbg());

  if (Jcallee->type() != callee->type() &&
      Jcallee->type()->as<Pi>()->codom()->isa<Sigma>()) {
    auto val = world_.extract(Japp, u64(0), app->dbg());
    auto pullback = world_.extract(Japp, u64(1), naming_.pullback(app));
    val2pullback_[val] = pullback;
    old2new_[app] = val;
    return val;
  }

  old2new_[app] = Japp;
  return Japp;
}

const Def *Algo::J_Tuple(const Tuple *tuple, const Scope &scope) {
  auto ops = tuple->ops();
  DefArr Jops{ops.size(),
              [this, &ops, &scope](auto i) { return J(ops[i], scope); }};
  auto Jtuple = world_.tuple(Jops, tuple->dbg());
  old2new_[tuple] = Jtuple;
  return Jtuple;
}

const Def *Algo::J_Pack(const Pack *pack, const Scope &scope) {
  auto Jbody = J(pack->body(), scope);
  auto Jshape = J(pack->shape(), scope);
  auto Jpack = world_.pack(Jbody, Jshape, pack->dbg());
  old2new_[pack] = Jpack;
  return Jpack;
}

const Def *Algo::J_Insert(const Insert *insert, const Scope &scope) {
  auto Jtuple = J(insert->tuple(), scope);
  auto Jindex = J(insert->index(), scope);
  auto Jvalue = J(insert->value(), scope);
  auto Jinsert = world_.insert(Jtuple, Jindex, Jvalue, insert->dbg());
  old2new_[insert] = Jinsert;
  return Jinsert;
}

const Def *Algo::J_Extract(const Extract *extract, const Scope &scope) {
  auto Jtuple = J(extract->tuple(), scope);
  auto Jindex = J(extract->index(), scope);
  auto Jextract = world_.insert(Jtuple, Jindex, extract->dbg());
  old2new_[extract] = Jextract;
  return Jextract;
}

// ========== Partial Tangents

void Algo::init_tangent_zero(Lam *primal_lam, const Def *val,
                             const Def *tangent_type) {
  auto mem = *primal2mem_[primal_lam];
  auto [mem2, ptr] = world_.op_alloc(tangent_type, mem)->split<2>();
  auto mem3 = world_.op_store(mem2, ptr, tangent_zero(tangent_type));

  primal2mem_[primal_lam] = mem3;
  val2global_tangent_[val] = ptr;
}

const Def *Algo::tangent_zero(const Def *tangent_type) {
  if (isa_sized_type(tangent_type)) {
    return world_.lit_real(r64(0.0));
  }

  if (auto sigma = tangent_type->isa<Sigma>()) {
    auto ops = sigma->ops();
    DefArr zero_ops{ops.size(),
                    [this, &ops](auto i) { return tangent_zero(ops[i]); }};
    return world_.sigma(zero_ops);
  }

  THORIN_UNREACHABLE;
}

const Def *Algo::tangent_plus(const Def *tangent_type, const Def *a,
                              const Def *b) {
  if (isa_sized_type(tangent_type)) {
    assert(a->type() == tangent_type);
    assert(b->type() == tangent_type);
    return world_.op(ROp::add, 0, a, b);
  }

  if (auto sigma = tangent_type->isa<Sigma>()) {
    auto ops = sigma->ops();
    auto mk_add = [this, &ops, a, b](auto i) {
      auto type = ops[i];
      auto a_op = a->op(i);
      auto b_op = b->op(i);
      assert(a_op->type() == type);
      assert(b_op->type() == type);
      return tangent_plus(type, a_op, b_op);
    };
    DefArr zero_ops{ops.size(), mk_add};
    return world_.sigma(zero_ops);
  }

  THORIN_UNREACHABLE;
}

DefDefArr Algo::collect_local_tangents(Lam *primal) {
  (void)primal;
  return {}; // TODO
}

const Def *Algo::update_global_tangents(const Def *mem,
                                        const DefDefArr &local_tangents) {
  for (auto &[val, loc_tan] : local_tangents) {
    if (auto ptr = val2global_tangent_.lookup(val)) {
      auto dbg = world_.dbg("glob_∂" + val->debug().name);
      auto [mem2, glob_tan] = world_.op_load(mem, *ptr, dbg)->split<2>();
      auto new_glob_tan = tangent_plus(loc_tan->type(), loc_tan, glob_tan);
      mem = world_.op_store(mem2, *ptr, new_glob_tan);
    }
  }

  return mem;
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

const Def *Algo::replace_front(const Def *target, const Def *def) {
  return target->isa<Tuple>() ? world_.insert(target, u64(0), def) : def;
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
