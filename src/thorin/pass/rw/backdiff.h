#ifndef THORIN_PASS_BACKDIFF_H
#define THORIN_PASS_BACKDIFF_H

#include "thorin/pass/pass.h"

namespace thorin {

class BackDiff : public RWPass {
  public:
    BackDiff(PassMan &man) : RWPass(man, "backdiff") {}
    const Def *rewrite(const Def *def) override;
};

} // namespace thorin

#endif // THORIN_PASS_BACKDIFF_H
