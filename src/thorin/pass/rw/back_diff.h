#ifndef THORIN_PASS_BACKDIFF_H
#define THORIN_PASS_BACKDIFF_H

#include "thorin/pass/pass.h"

namespace thorin {

class BackDiff : public RWPass {
  public:
    BackDiff(PassMan &man) : RWPass(man, "back_diff") {}

    const Def *rewrite(const Def *) override;
};

} // namespace thorin

#endif // THORIN_PASS_BACKDIFF_H

