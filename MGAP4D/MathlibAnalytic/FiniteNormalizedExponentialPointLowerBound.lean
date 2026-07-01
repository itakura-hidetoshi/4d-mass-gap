import MGAP4D.MathlibAnalytic.FiniteNormalizedExponentialOscillation
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A uniform oscillation bound on finite log-weights gives a pointwise lower
bound against the uniform distribution. -/
theorem finiteNormalizedExp_lower_of_oscillation
    {X : Type*} [Fintype X] [Nonempty X]
    (logWeight : X → ℝ)
    (R : ℝ)
    (hOsc : ∀ x y : X, logWeight x - logWeight y ≤ R)
    (x : X) :
    (Fintype.card X : ℝ)⁻¹ * Real.exp (-R) ≤
      finiteNormalizedExp logWeight x := by
  have hCompare :=
    finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
      logWeight (fun _ : X => 0) R (by
        intro y z
        simpa using hOsc y z) x
  have hUniform :
      finiteNormalizedExp (fun _ : X => 0) x =
        (Fintype.card X : ℝ)⁻¹ := by
    simp [finiteNormalizedExp, finiteExpPartition]
  have hDiv :
      finiteNormalizedExp (fun _ : X => 0) x / Real.exp R ≤
        finiteNormalizedExp logWeight x :=
    (div_le_iff₀ (Real.exp_pos R)).2 hCompare.2
  rw [hUniform] at hDiv
  simpa [Real.exp_neg, div_eq_mul_inv] using hDiv

/-- On the two-element gauge group, oscillation radius `R` gives the explicit
point lower bound `exp(-R) / 2`. -/
theorem z2Gauge_finiteNormalizedExp_lower_of_oscillation
    (logWeight : Z2Gauge → ℝ)
    (R : ℝ)
    (hOsc : ∀ x y : Z2Gauge, logWeight x - logWeight y ≤ R)
    (x : Z2Gauge) :
    Real.exp (-R) / 2 ≤ finiteNormalizedExp logWeight x := by
  have h := finiteNormalizedExp_lower_of_oscillation logWeight R hOsc x
  have hCard : Fintype.card Z2Gauge = 2 := by
    native_decide
  calc
    Real.exp (-R) / 2 =
        (Fintype.card Z2Gauge : ℝ)⁻¹ * Real.exp (-R) := by
      rw [hCard]
      ring
    _ ≤ finiteNormalizedExp logWeight x := h

end

end MathlibAnalytic
end MGAP4D
