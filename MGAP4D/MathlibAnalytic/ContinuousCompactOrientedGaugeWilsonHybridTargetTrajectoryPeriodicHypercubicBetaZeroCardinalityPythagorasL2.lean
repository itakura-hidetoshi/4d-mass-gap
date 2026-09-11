import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityProjectorInnerOrthogonalityL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite pairwise-orthogonal family in a real inner-product space satisfies
Pythagoras: the squared norm of its sum is the sum of the squared norms. -/
theorem finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (v : ι → V)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hTail :
          ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0 := by
        intro i hi j hj hij
        exact hOrth i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      have hHeadTail : inner ℝ (v a) (∑ i ∈ s, v i) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        apply hOrth a (Finset.mem_insert_self a s)
          i (Finset.mem_insert_of_mem hi)
        intro hai
        subst i
        exact ha hi
      have hTailHead : inner ℝ (∑ i ∈ s, v i) (v a) = 0 := by
        calc
          inner ℝ (∑ i ∈ s, v i) (v a) =
              inner ℝ (v a) (∑ i ∈ s, v i) := real_inner_comm _ _
          _ = 0 := hHeadTail
      calc
        ‖∑ i ∈ insert a s, v i‖ ^ 2 =
            ‖v a + ∑ i ∈ s, v i‖ ^ 2 := by
              rw [Finset.sum_insert ha]
        _ = ‖v a‖ ^ 2 + ‖∑ i ∈ s, v i‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_add_left, inner_add_right, hHeadTail, hTailHead,
            real_inner_self_eq_norm_sq, add_zero, zero_add]
        _ = ‖v a‖ ^ 2 + ∑ i ∈ s, ‖v i‖ ^ 2 := by
          rw [ih hTail]
        _ = ∑ i ∈ insert a s, ‖v i‖ ^ 2 := by
          rw [Finset.sum_insert ha]

/-- Every actual beta-zero Gibbs `L²` vector has an exact finite Pythagoras
identity across the `325` cardinality-sector components. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_eq_sum_range_norm_fluctuationCardinalityProjectorL2_sq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f‖ ^ 2 =
      ∑ k ∈ Finset.range 325,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f‖ ^ 2 := by
  have hDecomposition :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_apply_eq
      f
  calc
    ‖f‖ ^ 2 =
        ‖∑ k ∈ Finset.range 325,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k f‖ ^ 2 := by
      exact (congrArg (fun g => ‖g‖ ^ 2) hDecomposition).symm
    _ = ∑ k ∈ Finset.range 325,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f‖ ^ 2 := by
      apply finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      intro k _hk l _hl hkl
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_same_input_eq_zero_of_ne
          k l hkl f

/-- Compact receipt for the exact finite beta-zero cardinality Pythagoras
identity. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityPythagorasL2Receipt :
    Prop :=
  ∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    ‖f‖ ^ 2 =
      ∑ k ∈ Finset.range 325,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f‖ ^ 2

/-- The actual finite beta-zero cardinality Pythagoras receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityPythagorasL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityPythagorasL2Receipt := by
  intro f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_eq_sum_range_norm_fluctuationCardinalityProjectorL2_sq
      f

end

end MathlibAnalytic
end MGAP4D
