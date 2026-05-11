import MGAP4D.R6.Concrete.IntervalTheoremChecklist

namespace MGAP4D
namespace R6
namespace Concrete

structure IntervalProofObligationMap where
  r5BridgeToFutureModule : Prop
  vacuumSideToFutureModule : Prop
  excitedSideToFutureModule : Prop
  intervalBoundaryToFutureModule : Prop
  intervalExclusionToFutureModule : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityLinked : Prop
  publicBoundaryLinked : Prop

def IntervalProofObligationMap.ready (M : IntervalProofObligationMap) : Prop :=
  M.r5BridgeToFutureModule ∧ M.vacuumSideToFutureModule ∧ M.excitedSideToFutureModule ∧
  M.intervalBoundaryToFutureModule ∧ M.intervalExclusionToFutureModule ∧
  M.mathlibRequestLinked ∧ M.statusCompatibilityLinked ∧ M.publicBoundaryLinked

theorem interval_proof_obligation_map_pack
    (M : IntervalProofObligationMap) :
    M.ready ↔ M.r5BridgeToFutureModule ∧ M.vacuumSideToFutureModule ∧ M.excitedSideToFutureModule ∧
      M.intervalBoundaryToFutureModule ∧ M.intervalExclusionToFutureModule ∧
      M.mathlibRequestLinked ∧ M.statusCompatibilityLinked ∧ M.publicBoundaryLinked := by
  rfl

end Concrete
end R6
end MGAP4D
