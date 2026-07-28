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

/-- The canonical real inner product induced by Mathlib's inner-product-space
structure on the algebraic tensor complexification.  It is named explicitly to
avoid depending on a non-definitional equality between two available `Inner`
instances. -/
def realInner (x y : Space H) : ℝ :=
  @inner ℝ (Space H) InnerProductSpace.toInner x y

@[simp] theorem realInner_zero_left (x : Space H) :
    realInner 0 x = 0 := by
  simp [realInner]

@[simp] theorem realInner_zero_right (x : Space H) :
    realInner x 0 = 0 := by
  simp [realInner]

@[simp] theorem realInner_neg_right (x y : Space H) :
    realInner x (-y) = -realInner x y := by
  simp [realInner]

/-- Symmetry of the canonical real tensor inner product. -/
theorem realInner_comm (x y : Space H) :
    realInner x y = realInner y x := by
  unfold realInner
  exact (real_inner_comm x y).symm

/-- Additivity of the canonical real tensor inner product in the first
argument. -/
theorem realInner_add_left (x y z : Space H) :
    realInner (x + y) z = realInner x z + realInner y z := by
  unfold realInner
  exact inner_add_left x y z

/-- The canonical real embedding into the algebraic complexification is an
isometry. -/
noncomputable def ofRealLinearIsometry : H →ₗᵢ[ℝ] Space H where
  toLinearMap :=
    { toFun := fun x => (1 : ℂ) ⊗ₜ[ℝ] x
      map_add' := by
        intro x y
        exact TensorProduct.tmul_add (1 : ℂ) x y
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
    rw [imaginaryUnitLinearIsometry_tmul]
    change (Complex.I * z) ⊗ₜ[ℝ] y =
      (Complex.I * z) ⊗ₜ[ℝ] y
    rfl
  · intro x y hx hy
    rw [map_add, smul_add, hx, hy]

/-- The canonical complex structure squares to minus the identity. -/
@[simp] theorem imaginaryUnitLinearIsometry_sq_apply
    (x : Space H) :
    imaginaryUnitLinearIsometry (imaginaryUnitLinearIsometry x) = -x := by
  rw [imaginaryUnitLinearIsometry_apply_eq_smul,
    imaginaryUnitLinearIsometry_apply_eq_smul]
  simp [smul_smul]

/-- Multiplication by `i` preserves the canonical real tensor inner product. -/
@[simp] theorem realInner_imaginaryUnitLinearIsometry
    (x y : Space H) :
    realInner (imaginaryUnitLinearIsometry x)
        (imaginaryUnitLinearIsometry y) =
      realInner x y := by
  unfold realInner
  exact (imaginaryUnitLinearIsometry (H := H)).inner_map_map x y

/-- The orthogonal complex structure is skew-symmetric for the underlying real
inner product. -/
theorem realInner_imaginaryUnitLinearIsometry_left_eq_neg_right
    (x y : Space H) :
    realInner (imaginaryUnitLinearIsometry x) y =
      -realInner x (imaginaryUnitLinearIsometry y) := by
  have h := realInner_imaginaryUnitLinearIsometry x
    (imaginaryUnitLinearIsometry y)
  rw [imaginaryUnitLinearIsometry_sq_apply] at h
  rw [realInner_neg_right] at h
  linarith

/-- The real inner product of `Jx` with `x` vanishes. -/
@[simp] theorem realInner_imaginaryUnitLinearIsometry_self
    (x : Space H) :
    realInner (imaginaryUnitLinearIsometry x) x = 0 := by
  have hskew :=
    realInner_imaginaryUnitLinearIsometry_left_eq_neg_right x x
  have hsym :
      realInner x (imaginaryUnitLinearIsometry x) =
        realInner (imaginaryUnitLinearIsometry x) x :=
    realInner_comm x (imaginaryUnitLinearIsometry x)
  linarith

/-- Candidate complex inner product reconstructed from the underlying real
inner product and the orthogonal complex structure. -/
def complexInner (x y : Space H) : ℂ :=
  (realInner x y : ℂ) +
    Complex.I * (realInner (imaginaryUnitLinearIsometry x) y : ℂ)

@[simp] theorem complexInner_re (x y : Space H) :
    (complexInner x y).re = realInner x y := by
  simp [complexInner]

@[simp] theorem complexInner_im (x y : Space H) :
    (complexInner x y).im =
      realInner (imaginaryUnitLinearIsometry x) y := by
  simp [complexInner]

/-- On the diagonal, the candidate complex inner product is exactly the real
squared norm, embedded into `ℂ`. -/
@[simp] theorem complexInner_self (x : Space H) :
    complexInner x x = (realInner x x : ℂ) := by
  simp [complexInner]

/-- The candidate complex inner product is positive definite. -/
theorem complexInner_self_eq_zero_iff (x : Space H) :
    complexInner x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [complexInner_self] at h
    have hr : realInner x x = 0 := by
      exact_mod_cast h
    unfold realInner at hr
    exact inner_self_eq_zero.mp hr
  · rintro rfl
    simp [complexInner, realInner]

/-- The candidate complex inner product is Hermitian. -/
theorem complexInner_star_symm (x y : Space H) :
    star (complexInner y x) = complexInner x y := by
  apply Complex.ext
  · simp [complexInner, realInner_comm]
  · simp [complexInner]
    have h :=
      realInner_imaginaryUnitLinearIsometry_left_eq_neg_right y x
    rw [realInner_comm y (imaginaryUnitLinearIsometry x)] at h
    linarith

/-- The candidate complex inner product is additive in its first argument. -/
theorem complexInner_add_left (x y z : Space H) :
    complexInner (x + y) z = complexInner x z + complexInner y z := by
  simp only [complexInner, map_add, realInner_add_left]
  push_cast
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
