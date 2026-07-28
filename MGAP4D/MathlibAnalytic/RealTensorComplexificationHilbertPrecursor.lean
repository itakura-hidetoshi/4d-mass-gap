import MGAP4D.MathlibAnalytic.RealTensorComplexificationLinearMap
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace RealTensorComplexification

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real tensor-product inner product on pure tensors in the algebraic
complexification. -/
@[simp] theorem real_inner_tmul
    (z w : ℂ) (x y : H) :
    inner ℝ (z ⊗ₜ[ℝ] x : Space H) (w ⊗ₜ[ℝ] y) =
      inner ℝ z w * inner ℝ x y :=
  TensorProduct.inner_tmul ℝ z w x y

/-- The canonical real embedding into the algebraic complexification is an
isometry. -/
noncomputable def ofRealLinearIsometry : H →ₗᵢ[ℝ] Space H where
  toLinearMap :=
    { toFun := fun x => (1 : ℂ) ⊗ₜ[ℝ] x
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp }
  norm_map' := by
    intro x
    simp

@[simp] theorem ofRealLinearIsometry_apply (x : H) :
    ofRealLinearIsometry x = (1 : ℂ) ⊗ₜ[ℝ] x :=
  rfl

/-- Multiplication by `i` on `ℂ`, regarded as a real linear isometry. -/
noncomputable def complexIMulLinearIsometry : ℂ →ₗᵢ[ℝ] ℂ where
  toLinearMap :=
    { toFun := fun z => Complex.I * z
      map_add' := by
        intro z w
        ring
      map_smul' := by
        intro r z
        change Complex.I * ((r : ℂ) * z) =
          (r : ℂ) * (Complex.I * z)
        ring }
  norm_map' := by
    intro z
    simp

@[simp] theorem complexIMulLinearIsometry_apply (z : ℂ) :
    complexIMulLinearIsometry z = Complex.I * z :=
  rfl

/-- The orthogonal complex structure `J`, induced by multiplication by `i` on
 the scalar tensor factor. -/
noncomputable def imaginaryUnitLinearIsometry :
    Space H →ₗᵢ[ℝ] Space H :=
  TensorProduct.mapIsometry complexIMulLinearIsometry
    (LinearIsometry.id : H →ₗᵢ[ℝ] H)

@[simp] theorem imaginaryUnitLinearIsometry_tmul
    (z : ℂ) (x : H) :
    imaginaryUnitLinearIsometry (z ⊗ₜ[ℝ] x : Space H) =
      (Complex.I * z) ⊗ₜ[ℝ] x := by
  simp [imaginaryUnitLinearIsometry]

/-- The tensor-product complex structure is the ambient complex scalar action
by `i`. -/
theorem imaginaryUnitLinearIsometry_apply_eq_smul
    (x : Space H) :
    imaginaryUnitLinearIsometry x = Complex.I • x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z y
    simp
  · intro x y hx hy
    simp [map_add, hx, hy, add_comm]

/-- The canonical complex structure squares to minus the identity. -/
@[simp] theorem imaginaryUnitLinearIsometry_sq_apply
    (x : Space H) :
    imaginaryUnitLinearIsometry (imaginaryUnitLinearIsometry x) = -x := by
  rw [imaginaryUnitLinearIsometry_apply_eq_smul,
    imaginaryUnitLinearIsometry_apply_eq_smul]
  simp [smul_smul]

/-- Multiplication by `i` preserves the real tensor-product inner product. -/
@[simp] theorem inner_imaginaryUnitLinearIsometry
    (x y : Space H) :
    inner ℝ (imaginaryUnitLinearIsometry x)
        (imaginaryUnitLinearIsometry y) =
      inner ℝ x y := by
  simpa [imaginaryUnitLinearIsometry] using
    TensorProduct.inner_map_map complexIMulLinearIsometry
      (LinearIsometry.id : H →ₗᵢ[ℝ] H) x y

/-- The orthogonal complex structure is skew-symmetric for the underlying real
inner product. -/
theorem inner_imaginaryUnitLinearIsometry_left_eq_neg_right
    (x y : Space H) :
    inner ℝ (imaginaryUnitLinearIsometry x) y =
      -inner ℝ x (imaginaryUnitLinearIsometry y) := by
  have h := inner_imaginaryUnitLinearIsometry x
    (imaginaryUnitLinearIsometry y)
  rw [imaginaryUnitLinearIsometry_sq_apply] at h
  simp only [inner_neg_right] at h
  linarith

/-- The real inner product of `Jx` with `x` vanishes. -/
@[simp] theorem inner_imaginaryUnitLinearIsometry_self
    (x : Space H) :
    inner ℝ (imaginaryUnitLinearIsometry x) x = 0 := by
  have hskew :=
    inner_imaginaryUnitLinearIsometry_left_eq_neg_right x x
  have hsym :
      inner ℝ x (imaginaryUnitLinearIsometry x) =
        inner ℝ (imaginaryUnitLinearIsometry x) x :=
    real_inner_comm _ _
  linarith

/-- Candidate complex inner product reconstructed from the underlying real
inner product and the orthogonal complex structure. -/
def complexInner (x y : Space H) : ℂ :=
  (inner ℝ x y : ℂ) +
    Complex.I * (inner ℝ (imaginaryUnitLinearIsometry x) y : ℂ)

@[simp] theorem complexInner_re (x y : Space H) :
    (complexInner x y).re = inner ℝ x y := by
  simp [complexInner]

@[simp] theorem complexInner_im (x y : Space H) :
    (complexInner x y).im =
      inner ℝ (imaginaryUnitLinearIsometry x) y := by
  simp [complexInner]

/-- On the diagonal, the candidate complex inner product is exactly the real
squared norm, embedded into `ℂ`. -/
@[simp] theorem complexInner_self (x : Space H) :
    complexInner x x = (inner ℝ x x : ℂ) := by
  simp [complexInner]

/-- The candidate complex inner product is positive definite. -/
theorem complexInner_self_eq_zero_iff (x : Space H) :
    complexInner x x = 0 ↔ x = 0 := by
  rw [complexInner_self]
  simp [inner_self_eq_zero]

/-- The candidate complex inner product is Hermitian. -/
theorem complexInner_conj_symm (x y : Space H) :
    Complex.conj (complexInner y x) = complexInner x y := by
  apply Complex.ext
  · simp [complexInner, real_inner_comm]
  · simp [complexInner]
    have h :=
      inner_imaginaryUnitLinearIsometry_left_eq_neg_right y x
    rw [real_inner_comm y (imaginaryUnitLinearIsometry x)] at h
    linarith

/-- The candidate complex inner product is additive in its first argument. -/
theorem complexInner_add_left (x y z : Space H) :
    complexInner (x + y) z = complexInner x z + complexInner y z := by
  simp [complexInner, map_add]
  ring

/-- Every complex-linear map between algebraic complexifications commutes with
 the canonical complex structure. -/
theorem linearMap_map_imaginaryUnit
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (T : Space H →ₗ[ℂ] Space K)
    (x : Space H) :
    T (imaginaryUnitLinearIsometry x) =
      imaginaryUnitLinearIsometry (T x) := by
  rw [imaginaryUnitLinearIsometry_apply_eq_smul,
    imaginaryUnitLinearIsometry_apply_eq_smul]
  exact T.map_smul Complex.I x

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
