import MGAP4D.MathlibAnalytic.RealTensorComplexificationHilbertPrecursor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace RealTensorComplexification

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The existing real tensor norm is induced by the explicitly named canonical
real tensor inner product. -/
theorem norm_sq_eq_realInner (x : Space H) :
    ‖x‖ ^ 2 = realInner x x := by
  unfold realInner
  simpa using
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) x)

@[simp] theorem realInner_neg_left (x y : Space H) :
    realInner (-x) y = -realInner x y := by
  rw [realInner_comm, realInner_neg_right, realInner_comm]

@[simp] theorem realInner_real_smul_left
    (r : ℝ) (x y : Space H) :
    realInner (r • x) y = r * realInner x y := by
  unfold realInner
  simpa using (inner_smul_left (𝕜 := ℝ) x y (r := r))

/-- Decompose the ambient complex scalar action into its real and imaginary
parts using the canonical orthogonal complex structure. -/
theorem complex_smul_eq_re_add_im
    (c : ℂ) (x : Space H) :
    c • x = c.re • x + c.im • imaginaryUnitLinearIsometry x := by
  rw [imaginaryUnitLinearIsometry_apply_eq_smul]
  calc
    c • x = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • x := by
      rw [Complex.re_add_im]
    _ = (c.re : ℂ) • x + ((c.im : ℂ) * Complex.I) • x := by
      rw [add_smul]
    _ = c.re • x + c.im • (Complex.I • x) := by
      rw [mul_smul]
      change c.re • x + c.im • (Complex.I • x) =
        c.re • x + c.im • (Complex.I • x)
      rfl

/-- Real scalar multiplication is linear for the candidate complex inner
product. -/
theorem complexInner_real_smul_left
    (r : ℝ) (x y : Space H) :
    complexInner (r • x) y = (r : ℂ) * complexInner x y := by
  apply Complex.ext <;>
    simp [complexInner, realInner_real_smul_left, map_smul]

/-- Applying the canonical complex structure in the first variable multiplies
the candidate complex inner product by `-i`. -/
theorem complexInner_imaginaryUnit_left
    (x y : Space H) :
    complexInner (imaginaryUnitLinearIsometry x) y =
      -Complex.I * complexInner x y := by
  apply Complex.ext <;>
    simp [complexInner, realInner_neg_left]

/-- The candidate complex inner product is conjugate-linear in its first
variable for arbitrary complex scalars. -/
theorem complexInner_smul_left
    (c : ℂ) (x y : Space H) :
    complexInner (c • x) y = star c * complexInner x y := by
  rw [complex_smul_eq_re_add_im, complexInner_add_left,
    complexInner_real_smul_left, complexInner_real_smul_left,
    complexInner_imaginaryUnit_left]
  have hc : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    simpa [RCLike.star_def] using
      (RCLike.conj_eq_re_sub_im c)
  rw [hc]
  ring

/-- The candidate complex inner product is additive in its second variable. -/
theorem complexInner_add_right
    (x y z : Space H) :
    complexInner x (y + z) = complexInner x y + complexInner x z := by
  calc
    complexInner x (y + z) = star (complexInner (y + z) x) :=
      (complexInner_star_symm x (y + z)).symm
    _ = star (complexInner y x + complexInner z x) := by
      rw [complexInner_add_left]
    _ = complexInner x y + complexInner x z := by
      simp [complexInner_star_symm]

/-- The candidate complex inner product is complex-linear in its second
variable. -/
theorem complexInner_smul_right
    (c : ℂ) (x y : Space H) :
    complexInner x (c • y) = c * complexInner x y := by
  calc
    complexInner x (c • y) = star (complexInner (c • y) x) :=
      (complexInner_star_symm x (c • y)).symm
    _ = star (star c * complexInner y x) := by
      rw [complexInner_smul_left]
    _ = c * complexInner x y := by
      simp [complexInner_star_symm]

/-- Squared-norm compatibility for the ambient complex scalar action. -/
theorem norm_complex_smul_sq
    (c : ℂ) (x : Space H) :
    ‖c • x‖ ^ 2 = (‖c‖ * ‖x‖) ^ 2 := by
  rw [norm_sq_eq_realInner, ← complexInner_re,
    complexInner_smul_left, complexInner_smul_right,
    complexInner_self, ← mul_assoc]
  change (((star c * c) * (realInner x x : ℂ)).re) =
    (‖c‖ * ‖x‖) ^ 2
  rw [show star c * c = (‖c‖ ^ 2 : ℂ) by
    simpa [RCLike.star_def] using (RCLike.conj_mul c)]
  change ‖c‖ ^ 2 * realInner x x =
    (‖c‖ * ‖x‖) ^ 2
  rw [← norm_sq_eq_realInner x]
  ring

/-- The existing tensor norm is exactly homogeneous for the ambient complex
scalar action. -/
theorem norm_complex_smul
    (c : ℂ) (x : Space H) :
    ‖c • x‖ = ‖c‖ * ‖x‖ := by
  have hsq := norm_complex_smul_sq c x
  have hx : 0 ≤ ‖c • x‖ := norm_nonneg _
  have hcx : 0 ≤ ‖c‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Complex normed-space structure using the already existing real tensor
norm.  No replacement norm is introduced. -/
@[reducible] noncomputable def complexNormedSpace :
    NormedSpace ℂ (Space H) where
  norm_smul_le c x := by
    rw [norm_complex_smul]

/-- Complex inner-product-space structure on the algebraic tensor
complexification, compatible with the pre-existing real tensor norm. -/
@[reducible] noncomputable def complexInnerProductSpace :
    InnerProductSpace ℂ (Space H) where
  toNormedSpace := complexNormedSpace
  toInner := ⟨complexInner⟩
  norm_sq_eq_re_inner := fun x => by
    rw [norm_sq_eq_realInner]
    exact (complexInner_re x x).symm
  conj_inner_symm := fun x y => by
    change star (complexInner y x) = complexInner x y
    exact complexInner_star_symm x y
  add_left := complexInner_add_left
  smul_left := fun x y c => by
    change complexInner (c • x) y = star c * complexInner x y
    exact complexInner_smul_left c x y

noncomputable instance instComplexInnerProductSpace :
    InnerProductSpace ℂ (Space H) :=
  complexInnerProductSpace

@[simp] theorem inner_complex_eq_complexInner
    (x y : Space H) :
    inner ℂ x y = complexInner x y :=
  rfl

@[simp] theorem inner_complex_re
    (x y : Space H) :
    (inner ℂ x y).re = realInner x y := by
  rw [inner_complex_eq_complexInner, complexInner_re]

@[simp] theorem inner_complex_self
    (x : Space H) :
    inner ℂ x x = (realInner x x : ℂ) := by
  rw [inner_complex_eq_complexInner, complexInner_self]

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
