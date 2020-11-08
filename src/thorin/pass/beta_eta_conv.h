#ifndef THORIN_PASS_BETA_ETA_CONV_H
#define THORIN_PASS_BETA_ETA_CONV_H

#include "thorin/pass/pass.h"

namespace thorin {

/**
 * Performs β- and η-conversion.
 * It uses the following strategy:
 * * β-reduction of <code>f e</code>happens if <code>f</code> only occurs exactly once in the program in callee position.
 *   This happens optimistically within the big fixed-point loop.
 * * η-reduction:
 *      * <code>λx.e x -> e</code>, whenever <code>x</code> does not appear free in <code>e</code>.
 *        Right now however, @p BetaEtaConv will assume this if <code>e</code> is a @p Lam.
 *      * <code>f -> λx.f x</code>, if <code>f</code> is a @p Lam that does not appear in callee position.
 *       This rule is a generalization of critical edge elimination.
 *       It gives other @p Pass%es such as @p SSAConstr the opportunity to change <code>f</code>'s signature (e.g. adding or removing params).
 */

class BetaEtaConv : public Pass<BetaEtaConv> {
public:
    BetaEtaConv(PassMan& man, size_t index)
        : Pass(man, index, "reduction")
    {}

    const Def* rewrite(Def*, const Def*) override;
    undo_t analyze(Def*, const Def*) override;

    using Data = std::tuple<LamSet>;

private:
    LamSet keep_;
    Def2Def def2eta_;
    DefSet wrappers_;
};

}

#endif
