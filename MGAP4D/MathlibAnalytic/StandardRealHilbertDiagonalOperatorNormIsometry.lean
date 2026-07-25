import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalComplexification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Diagonal complexification preserves the operator norm. -/
@[simp]
theorem norm_diagonalComplexification (T : H →L[ℝ] H) :
    ‖diagonalComplexification T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro z
    apply
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg T) (norm_nonneg z))).mp
    change standardNorm (diagonalComplexification T z) ^ 2 ≤
      (‖T‖ * standardNorm z) ^ 2
    rw [mul_pow, standardNorm_sq, standardNorm_sq]
    simp only [diagonalComplexification_re, diagonalComplexification_im]
    have hre :
        ‖T z.1‖ ^ 2 ≤ (‖T‖ * ‖z.1‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg T) (norm_nonneg z.1))).2
        (T.le_opNorm z.1)
    have him :
        ‖T z.2‖ ^ 2 ≤ (‖T‖ * ‖z.2‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg T) (norm_nonneg z.2))).2
        (T.le_opNorm z.2)
    rw [mul_pow] at hre him
    nlinarith
  · refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _) ?_
    intro x
    calc
      ‖T x‖ = ‖ofReal (T x)‖ := (norm_ofReal (T x)).symm
      _ = ‖diagonalComplexification T (ofReal x)‖ := by
        rw [diagonalComplexification_ofReal]
      _ ≤ ‖diagonalComplexification T‖ * ‖ofReal x‖ :=
        (diagonalComplexification T).le_opNorm _
      _ = ‖diagonalComplexification T‖ * ‖x‖ := by
        rw [norm_ofReal]

/-- Diagonal complexification also preserves the nonnegative operator norm. -/
@[simp]
theorem nnnorm_diagonalComplexification (T : H →L[ℝ] H) :
    ‖diagonalComplexification T‖₊ = ‖T‖₊ :=
  Subtype.ext (norm_diagonalComplexification T)

/-- Diagonal complexification is injective on bounded real-linear endomorphisms. -/
theorem diagonalComplexification_injective :
    Function.Injective (diagonalComplexification (H := H)) := by
  intro S T h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun A => A (ofReal x)) h
  simpa using congrArg Prod.fst hx

/-- Diagonal complexification vanishes exactly when the original operator vanishes. -/
@[simp]
theorem diagonalComplexification_eq_zero_iff (T : H →L[ℝ] H) :
    diagonalComplexification T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← norm_diagonalComplexification T, h, norm_zero]
  · rintro rfl
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext <;> simp

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
