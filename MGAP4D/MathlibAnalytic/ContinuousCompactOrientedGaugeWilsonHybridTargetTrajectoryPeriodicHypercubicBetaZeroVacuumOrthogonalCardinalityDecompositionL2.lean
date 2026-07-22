import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityPythagorasL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- If the zeroth term vanishes, a finite range sum can be reindexed over the
strictly positive terms. -/
theorem finset_sum_range_succ_eq_shifted_sum_of_zero
    {M : Type*}
    [AddCommMonoid M]
    (v : ℕ → M)
    (n : ℕ)
    (hZero : v 0 = 0) :
    (∑ k ∈ Finset.range (n + 1), v k) =
      ∑ k ∈ Finset.range n, v (k + 1) := by
  rw [Finset.sum_range_succ', hZero, add_zero]

/-- A Gibbs `L²` vector orthogonal to the normalized vacuum is reconstructed
entirely from its positive-cardinality components. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_positive_fluctuationCardinalityProjectorL2_apply_eq_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    (∑ k ∈ Finset.range 324,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        (k + 1) f) = f := by
  have hZero :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hShift :=
    finset_sum_range_succ_eq_shifted_sum_of_zero
      (fun k =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f)
      324 hZero
  calc
    (∑ k ∈ Finset.range 324,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        (k + 1) f) =
        ∑ k ∈ Finset.range 325,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k f := by
      simpa using hShift.symm
    _ = f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_apply_eq
        f

/-- On the vacuum-orthogonal subspace, the exact cardinality Pythagoras identity
contains only the `324` nonstationary sectors. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_eq_sum_positive_norm_fluctuationCardinalityProjectorL2_sq_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖f‖ ^ 2 =
      ∑ k ∈ Finset.range 324,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f‖ ^ 2 := by
  have hZero :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hZeroNorm :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f‖ ^ 2 = 0 := by
    simp [hZero]
  have hShift :=
    finset_sum_range_succ_eq_shifted_sum_of_zero
      (fun k =>
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f‖ ^ 2)
      324 hZeroNorm
  calc
    ‖f‖ ^ 2 =
        ∑ k ∈ Finset.range 325,
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k f‖ ^ 2 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_eq_sum_range_norm_fluctuationCardinalityProjectorL2_sq
        f
    _ = ∑ k ∈ Finset.range 324,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f‖ ^ 2 := by
      simpa using hShift

/-- Compact receipt for the exact positive-cardinality decomposition of every
vacuum-orthogonal beta-zero Gibbs `L²` vector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalCardinalityDecompositionL2Receipt :
    Prop :=
  ∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f = 0 →
      ((∑ k ∈ Finset.range 324,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f) = f) ∧
      (‖f‖ ^ 2 =
        ∑ k ∈ Finset.range 324,
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ ^ 2)

/-- The actual vacuum-orthogonal positive-cardinality decomposition receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalCardinalityDecompositionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalCardinalityDecompositionL2Receipt := by
  intro f hOrthogonal
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_positive_fluctuationCardinalityProjectorL2_apply_eq_of_inner_vacuum_eq_zero
      f hOrthogonal,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_eq_sum_positive_norm_fluctuationCardinalityProjectorL2_sq_of_inner_vacuum_eq_zero
      f hOrthogonal⟩

end

end MathlibAnalytic
end MGAP4D
