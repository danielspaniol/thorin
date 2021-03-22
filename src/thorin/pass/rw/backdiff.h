#ifndef THORIN_PASS_BACKDIFF_H
#define THORIN_PASS_BACKDIFF_H

#include "thorin/pass/pass.h"

namespace thorin {

class BackDiffNaming {
public:
  BackDiffNaming(World &world) : world_{world} {}

  const Def *primal(const Def *def);
  const Def *adjoint(const Def *def);
  const Def *pullback(const Def *def);
  const Def *back(const Def *def);
  const Def *tangent_init(const Def *def);

private:
  const Def *add_to_name(const Def *def, const std::string &str);

  World &world_;
};

class BackDiffTyping {
public:
  BackDiffTyping(World &world, Lam *src)
      : naming_{world}, world_{world}, final_ret_{nullptr}, src_{src} {}

  const Pi *final_ret();
  const Pi *back(const Pi *pi);

  const Pi *primal(Lam *lam);
  const Pi *primal(const Pi *pi);

  const Pi *pullback(Lam *lam);
  const Pi *pullback(const Pi *pi, const Pi *next_pi);

  const Pi *adjoint(Lam *lam);
  const Pi *adjoint(const Pi *pi, const Pi *next_pi);

  const Def *tangent(const Def *type);
  const Pi *tangent_init(Lam *orig_lam);

private:
  BackDiffNaming naming_;
  World &world_;
  const Pi *final_ret_;
  Lam *src_;
};

class BackDiff : public RWPass {
public:
  BackDiff(PassMan &man) : RWPass(man, "backdiff") {}
  const Def *rewrite(const Def *def) override;
};

} // namespace thorin

#endif // THORIN_PASS_BACKDIFF_H
