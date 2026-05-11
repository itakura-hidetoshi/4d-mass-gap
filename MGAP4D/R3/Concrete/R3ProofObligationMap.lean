import MGAP4D.R3.Concrete.R3TheoremChecklist

namespace MGAP4D
namespace R3
namespace Concrete

structure R3ProofObligationMap where
  shiftedToFutureModule : Prop
  nonnegativeToFutureModule : Prop
  zeroFormToFutureModule : Prop
  sqrtRouteToFutureModule : Prop
  bridgeToFutureModule : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityLinked : Prop
  publicBoundaryLinked : Prop

def R3ProofObligationMap.ready (M : R3ProofObligationMap) : Prop :=
  M.shiftedToFutureModule ∧ M.nonnegativeToFutureModule ∧ M.zeroFormToFutureModule ∧
  M.sqrtRouteToFutureModule ∧ M.bridgeToFutureModule ∧ M.mathlibRequestLinked ∧
  M.statusCompatibilityLinked ∧ M.publicBoundaryLinked

theorem r3_proof_obligation_map_pack
    (M : R3ProofObligationMap) :
    M.ready ↔ M.shiftedToFutureModule ∧ M.nonnegativeToFutureModule ∧ M.zeroFormToFutureModule ∧
      M.sqrtRouteToFutureModule ∧ M.bridgeToFutureModule ∧ M.mathlibRequestLinked ∧
      M.statusCompatibilityLinked ∧ M.publicBoundaryLinked := by
  rfl

end Concrete
end R3
end MGAP4D
