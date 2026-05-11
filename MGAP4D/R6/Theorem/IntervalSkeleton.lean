import MGAP4D.R6.Concrete.IntervalProofObligationMap

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalSkeleton where
  obligationMapReady : Prop
  r5BridgeTheoremTarget : Prop
  vacuumSideTheoremTarget : Prop
  excitedSideTheoremTarget : Prop
  intervalBoundaryTheoremTarget : Prop
  intervalExclusionTheoremTarget : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def IntervalSkeleton.ready (S : IntervalSkeleton) : Prop :=
  S.obligationMapReady ∧ S.r5BridgeTheoremTarget ∧ S.vacuumSideTheoremTarget ∧
  S.excitedSideTheoremTarget ∧ S.intervalBoundaryTheoremTarget ∧
  S.intervalExclusionTheoremTarget ∧ S.mathlibRequestLinked ∧
  S.statusCompatibilityHeld ∧ S.publicBoundaryHeld

theorem interval_skeleton_pack
    (S : IntervalSkeleton) :
    S.ready ↔ S.obligationMapReady ∧ S.r5BridgeTheoremTarget ∧ S.vacuumSideTheoremTarget ∧
      S.excitedSideTheoremTarget ∧ S.intervalBoundaryTheoremTarget ∧
      S.intervalExclusionTheoremTarget ∧ S.mathlibRequestLinked ∧
      S.statusCompatibilityHeld ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
