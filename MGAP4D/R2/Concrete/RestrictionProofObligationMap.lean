import MGAP4D.R2.Concrete.RestrictionTheoremChecklist

namespace MGAP4D
namespace R2
namespace Concrete

structure RestrictionProofObligationMap where
  reducingSubspaceToFutureModule : Prop
  fullHamiltonianSelfAdjointToFutureModule : Prop
  restrictionDomainToFutureModule : Prop
  restrictionOperatorToFutureModule : Prop
  restrictionSelfAdjointToFutureModule : Prop
  operatorAPIBridgeToFutureModule : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityLinked : Prop
  publicBoundaryLinked : Prop

def RestrictionProofObligationMap.ready (M : RestrictionProofObligationMap) : Prop :=
  M.reducingSubspaceToFutureModule ∧ M.fullHamiltonianSelfAdjointToFutureModule ∧
  M.restrictionDomainToFutureModule ∧ M.restrictionOperatorToFutureModule ∧
  M.restrictionSelfAdjointToFutureModule ∧ M.operatorAPIBridgeToFutureModule ∧
  M.mathlibRequestLinked ∧ M.statusCompatibilityLinked ∧ M.publicBoundaryLinked

theorem restriction_proof_obligation_map_pack
    (M : RestrictionProofObligationMap) :
    M.ready ↔ M.reducingSubspaceToFutureModule ∧ M.fullHamiltonianSelfAdjointToFutureModule ∧
      M.restrictionDomainToFutureModule ∧ M.restrictionOperatorToFutureModule ∧
      M.restrictionSelfAdjointToFutureModule ∧ M.operatorAPIBridgeToFutureModule ∧
      M.mathlibRequestLinked ∧ M.statusCompatibilityLinked ∧ M.publicBoundaryLinked := by
  rfl

end Concrete
end R2
end MGAP4D
