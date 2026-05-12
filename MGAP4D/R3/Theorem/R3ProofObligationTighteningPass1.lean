import MGAP4D.R3.Concrete.R3ProofObligationMap
import MGAP4D.R3.Theorem.R3HardeningPass

namespace MGAP4D
namespace R3
namespace Theorem

structure R3ProofObligationTighteningPass1 where
  sourceObligationMapVisible : Prop
  hardeningPassVisible : Prop
  shiftedRouteObligationSeparated : Prop
  zeroFormRouteObligationSeparated : Prop
  operatorBoundaryObligationSeparated : Prop
  bridgeObligationSeparated : Prop
  downstreamR4R7ReviewGateSeparated : Prop
  publicBoundaryObligationSeparated : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def R3ProofObligationTighteningPass1.ready
    (P : R3ProofObligationTighteningPass1) : Prop :=
  P.sourceObligationMapVisible ∧ P.hardeningPassVisible ∧
  P.shiftedRouteObligationSeparated ∧ P.zeroFormRouteObligationSeparated ∧
  P.operatorBoundaryObligationSeparated ∧ P.bridgeObligationSeparated ∧
  P.downstreamR4R7ReviewGateSeparated ∧ P.publicBoundaryObligationSeparated ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧
  P.theoremCompletionNotClaimed ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem r3_proof_obligation_tightening_pass1_pack
    (P : R3ProofObligationTighteningPass1) :
    P.ready ↔ P.sourceObligationMapVisible ∧ P.hardeningPassVisible ∧
      P.shiftedRouteObligationSeparated ∧ P.zeroFormRouteObligationSeparated ∧
      P.operatorBoundaryObligationSeparated ∧ P.bridgeObligationSeparated ∧
      P.downstreamR4R7ReviewGateSeparated ∧ P.publicBoundaryObligationSeparated ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧
      P.theoremCompletionNotClaimed ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R3
end MGAP4D
