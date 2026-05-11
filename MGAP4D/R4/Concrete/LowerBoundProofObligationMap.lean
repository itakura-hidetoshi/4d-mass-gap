import MGAP4D.R4.Concrete.LowerBoundTheoremChecklist

namespace MGAP4D
namespace R4
namespace Concrete

structure LowerBoundProofObligationMap where
  r2BridgeToFutureModule : Prop
  ledgerToFutureModule : Prop
  constantToFutureModule : Prop
  lowerBoundToFutureModule : Prop
  operatorBridgeToFutureModule : Prop
  estimateToFutureModule : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityLinked : Prop
  publicBoundaryLinked : Prop

def LowerBoundProofObligationMap.ready (M : LowerBoundProofObligationMap) : Prop :=
  M.r2BridgeToFutureModule ∧ M.ledgerToFutureModule ∧ M.constantToFutureModule ∧
  M.lowerBoundToFutureModule ∧ M.operatorBridgeToFutureModule ∧ M.estimateToFutureModule ∧
  M.mathlibRequestLinked ∧ M.statusCompatibilityLinked ∧ M.publicBoundaryLinked

theorem lower_bound_proof_obligation_map_pack
    (M : LowerBoundProofObligationMap) :
    M.ready ↔ M.r2BridgeToFutureModule ∧ M.ledgerToFutureModule ∧ M.constantToFutureModule ∧
      M.lowerBoundToFutureModule ∧ M.operatorBridgeToFutureModule ∧ M.estimateToFutureModule ∧
      M.mathlibRequestLinked ∧ M.statusCompatibilityLinked ∧ M.publicBoundaryLinked := by
  rfl

end Concrete
end R4
end MGAP4D
