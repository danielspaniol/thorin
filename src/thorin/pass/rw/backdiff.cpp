#include "backdiff.h"

namespace thorin {

////////////////////////////////////////////////////////////////////////////////
// IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////

namespace {

class Algo {
  public:
    Algo(World &world, Lam *lam);

    Lam *rewrite();

  private:
    World &world_;
    Lam *src_;
};

Algo::Algo(World &world, Lam *lam) : world_{world}, src_{lam} {}

Lam *Algo::rewrite() {
    return nullptr; // TODO
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
