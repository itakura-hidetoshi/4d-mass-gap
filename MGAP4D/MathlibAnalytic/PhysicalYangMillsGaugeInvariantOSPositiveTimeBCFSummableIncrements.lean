import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeBCFClosedCauchyLimit
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Summable control of consecutive positive-time BCF increments implies the
Cauchy property required by the closed-range continuum-limit constructor. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCF_cauchySeq_of_summable_increment_bound
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : ℕ → D.positiveTimeSubalgebra)
    (ε : ℕ → ℝ)
    (hstep : ∀ n,
      dist (D.positiveTimeBCF (F n)) (D.positiveTimeBCF (F n.succ)) ≤ ε n)
    (hε : Summable ε) :
    CauchySeq (fun n => D.positiveTimeBCF (F n)) := by
  exact cauchySeq_of_dist_le_of_summable ε hstep hε

/-- The exact consecutive distances may themselves be used as the summable
control sequence. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.positiveTimeBCF_cauchySeq_of_summable_dist
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : ℕ → D.positiveTimeSubalgebra)
    (h : Summable fun n =>
      dist (D.positiveTimeBCF (F n)) (D.positiveTimeBCF (F n.succ))) :
    CauchySeq (fun n => D.positiveTimeBCF (F n)) := by
  exact cauchySeq_of_summable_dist h

/-- For primitive normalized-trace cylinders, a summable bound on consecutive
physical BCF increments plus closedness of the positive-time BCF range
constructs a continuum positive-time observable and proves its OS quadratic
nonnegativity.

This replaces the abstract Cauchy receipt of the previous endpoint by a local,
scale-to-scale summability condition. -/
theorem normalizedTracePower_varying_exists_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_closedRange_summableIncrements
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta) (j : ℕ)
    (R : ∀ n, PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (hclosed : IsClosed D.positiveTimeBCFRange) (ε : ℕ → ℝ)
    (hstep : ∀ n, dist (D.positiveTimeBCF ((R n).positiveTimeTracePowerObservable j))
      (D.positiveTimeBCF ((R n.succ).positiveTimeTracePowerObservable j)) ≤ ε n)
    (hε : Summable ε) :
    ∃ Flim : D.positiveTimeSubalgebra,
      Tendsto (fun n => D.positiveTimeBCF ((R n).positiveTimeTracePowerObservable j))
        atTop (nhds (D.positiveTimeBCF Flim)) ∧
      0 ≤ ∫ A, D.quadraticBoundedContinuousFunction Flim A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  apply normalizedTracePower_varying_exists_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_closedRange_cauchy
    S D halfExtent beta hbeta G j R hclosed
  exact D.positiveTimeBCF_cauchySeq_of_summable_increment_bound
    (fun n => (R n).positiveTimeTracePowerObservable j) ε hstep hε

/-- A direct variant requiring summability of the exact consecutive BCF
distances. -/
theorem normalizedTracePower_varying_exists_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_closedRange_summableDist
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta) (j : ℕ)
    (R : ∀ n, PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (hclosed : IsClosed D.positiveTimeBCFRange)
    (hsum : Summable fun n => dist
      (D.positiveTimeBCF ((R n).positiveTimeTracePowerObservable j))
      (D.positiveTimeBCF ((R n.succ).positiveTimeTracePowerObservable j))) :
    ∃ Flim : D.positiveTimeSubalgebra,
      Tendsto (fun n => D.positiveTimeBCF ((R n).positiveTimeTracePowerObservable j))
        atTop (nhds (D.positiveTimeBCF Flim)) ∧
      0 ≤ ∫ A, D.quadraticBoundedContinuousFunction Flim A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  apply normalizedTracePower_varying_exists_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_closedRange_cauchy
    S D halfExtent beta hbeta G j R hclosed
  exact D.positiveTimeBCF_cauchySeq_of_summable_dist
    (fun n => (R n).positiveTimeTracePowerObservable j) hsum

end

end MathlibAnalytic
end MGAP4D
