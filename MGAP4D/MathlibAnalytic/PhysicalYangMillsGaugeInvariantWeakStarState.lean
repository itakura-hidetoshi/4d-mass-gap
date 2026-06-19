import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantContinuousState
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The `n`-th normalized positive gauge-invariant state, viewed in the
weak-star dual of the physical observable algebra. -/
noncomputable def physicalYangMillsApproximatingGaugeInvariantWeakStarState
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    WeakDual ℝ (physicalYangMillsGaugeInvariantObservableSubalgebra S) :=
  StrongDual.toWeakDual
    (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).
      toContinuousLinearMap

/-- The continuum normalized positive gauge-invariant state, viewed in the
weak-star dual of the physical observable algebra. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantWeakStarState
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    WeakDual ℝ (physicalYangMillsGaugeInvariantObservableSubalgebra S) :=
  StrongDual.toWeakDual
    (physicalYangMillsContinuumGaugeInvariantContinuousState S).
      toContinuousLinearMap

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantWeakStarState S n O =
      physicalYangMillsApproximatingGaugeInvariantExpectation S n O := by
  simp [physicalYangMillsApproximatingGaugeInvariantWeakStarState]

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantWeakStarState_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsContinuumGaugeInvariantWeakStarState S O =
      physicalYangMillsContinuumGaugeInvariantExpectation S O := by
  simp [physicalYangMillsContinuumGaugeInvariantWeakStarState]

/-- The embedded-lattice normalized positive gauge-invariant states converge to
the continuum state in the weak-star topology. -/
theorem physical_yang_mills_gaugeInvariantWeakStarState_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    Tendsto
      (fun n : ℕ =>
        physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
      atTop
      (nhds (physicalYangMillsContinuumGaugeInvariantWeakStarState S)) := by
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro O
  change Tendsto
    (fun n : ℕ =>
      physicalYangMillsApproximatingGaugeInvariantWeakStarState S n O)
    atTop
    (nhds (physicalYangMillsContinuumGaugeInvariantWeakStarState S O))
  simpa using
    physical_yang_mills_gaugeInvariantContinuousState_pointwise_converges S O

end

end MathlibAnalytic
end MGAP4D
