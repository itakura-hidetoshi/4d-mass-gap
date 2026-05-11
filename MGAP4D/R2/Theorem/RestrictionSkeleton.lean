import MGAP4D.R2.Concrete.RestrictionProofObligationMap

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionSkeleton where
  obligationMapReady : Prop
  reducingSubspaceTheoremTarget : Prop
  fullHamiltonianSelfAdjointTheoremTarget : Prop
  restrictionDomainTheoremTarget : Prop
  restrictionOperatorTheoremTarget : Prop
  restrictionSelfAdjointTheoremTarget : Prop
  operatorAPIBridgeTheoremTarget : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def RestrictionSkeleton.ready (S : RestrictionSkeleton) : Prop :=
  S.obligationMapReady ∧ S.reducingSubspaceTheoremTarget ∧
  S.fullHamiltonianSelfAdjointTheoremTarget ∧ S.restrictionDomainTheoremTarget ∧
  S.restrictionOperatorTheoremTarget ∧ S.restrictionSelfAdjointTheoremTarget ∧
  S.operatorAPIBridgeTheoremTarget ∧ S.mathlibRequestLinked ∧
  S.statusCompatibilityHeld ∧ S.publicBoundaryHeld

theorem restriction_skeleton_pack
    (S : RestrictionSkeleton) :
    S.ready ↔ S.obligationMapReady ∧ S.reducingSubspaceTheoremTarget ∧
      S.fullHamiltonianSelfAdjointTheoremTarget ∧ S.restrictionDomainTheoremTarget ∧
      S.restrictionOperatorTheoremTarget ∧ S.restrictionSelfAdjointTheoremTarget ∧
      S.operatorAPIBridgeTheoremTarget ∧ S.mathlibRequestLinked ∧
      S.statusCompatibilityHeld ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
