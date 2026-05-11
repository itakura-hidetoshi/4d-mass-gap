import MGAP4D.R4.Concrete.LowerBoundProofObligationMap

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundSkeleton where
  obligationMapReady : Prop
  r2BridgeTheoremTarget : Prop
  ledgerTheoremTarget : Prop
  constantTheoremTarget : Prop
  lowerBoundTheoremTarget : Prop
  operatorBridgeTheoremTarget : Prop
  estimateTheoremTarget : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def LowerBoundSkeleton.ready (S : LowerBoundSkeleton) : Prop :=
  S.obligationMapReady ∧ S.r2BridgeTheoremTarget ∧ S.ledgerTheoremTarget ∧
  S.constantTheoremTarget ∧ S.lowerBoundTheoremTarget ∧ S.operatorBridgeTheoremTarget ∧
  S.estimateTheoremTarget ∧ S.mathlibRequestLinked ∧
  S.statusCompatibilityHeld ∧ S.publicBoundaryHeld

theorem lower_bound_skeleton_pack
    (S : LowerBoundSkeleton) :
    S.ready ↔ S.obligationMapReady ∧ S.r2BridgeTheoremTarget ∧ S.ledgerTheoremTarget ∧
      S.constantTheoremTarget ∧ S.lowerBoundTheoremTarget ∧ S.operatorBridgeTheoremTarget ∧
      S.estimateTheoremTarget ∧ S.mathlibRequestLinked ∧
      S.statusCompatibilityHeld ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
