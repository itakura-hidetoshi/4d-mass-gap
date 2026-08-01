import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMixedDysonResponse
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Uniform factorial bound for a mixed-direction Dyson polarization
coefficient.  Every direction is controlled by the same envelope `h`, while
`M` controls the real resolvent norm. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonCoefficient_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z M h : ℝ)
    (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M)
    (hH : ∀ i, ‖H i‖ ≤ h) :
    ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z‖ ≤
      (n.factorial : ℝ) * (M * h) ^ n * M := by
  induction n with
  | zero =>
      simpa [continuousLinearMapRealResolventOperatorMixedDysonCoefficient] using hR
  | succ n ih =>
      rw [continuousLinearMapRealResolventOperatorMixedDysonCoefficient_succ]
      calc
        ‖∑ i : Fin (n + 1),
            continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
                (fun j => H (i.succAbove j)) z *
              H i * continuousLinearMapRealResolvent A z‖ ≤
            ∑ i : Fin (n + 1),
              ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
                  (fun j => H (i.succAbove j)) z *
                H i * continuousLinearMapRealResolvent A z‖ := by
          simpa using
            norm_sum_le (Finset.univ : Finset (Fin (n + 1)))
              (fun i =>
                continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
                    (fun j => H (i.succAbove j)) z *
                  H i * continuousLinearMapRealResolvent A z)
        _ ≤ ∑ _i : Fin (n + 1),
              (n.factorial : ℝ) * (M * h) ^ n * M * h * M := by
          apply Finset.sum_le_sum
          intro i _hi
          calc
            ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
                  (fun j => H (i.succAbove j)) z *
                H i * continuousLinearMapRealResolvent A z‖ ≤
                (‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A
                    (fun j => H (i.succAbove j)) z‖ * ‖H i‖) *
                  ‖continuousLinearMapRealResolvent A z‖ := by
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ ((n.factorial : ℝ) * (M * h) ^ n * M * h) * M := by
              gcongr
              · exact ih (fun j => H (i.succAbove j))
                  (fun j => hH (i.succAbove j))
              · exact hH i
            _ = (n.factorial : ℝ) * (M * h) ^ n * M * h * M := by ring
        _ = (Nat.factorial (n + 1) : ℝ) * (M * h) ^ (n + 1) * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
          ring

/-- The factorial envelope used for the operator norm of the symmetric
mixed-direction Dyson carrier. -/
def continuousLinearMapRealResolventMixedDysonMultilinearBound
    (n : ℕ) (M : ℝ) : ℝ :=
  (n.factorial : ℝ) * M ^ (n + 1)

end MathlibAnalytic
end MGAP4D
