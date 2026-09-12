import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedRealTraceInversion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Charge conjugation on `SU(N)`

For a unitary matrix, entrywise complex conjugation is equivalently the transpose of its inverse.
We therefore define the finite-Wilson charge-conjugation involution by

`C(U) = transpose (U⁻¹)`.

This presentation uses only the existing group inverse and matrix-transpose APIs, so preservation of
unitarity and determinant one is immediate.  We prove involutivity, compatibility with
multiplication and inversion, identify the underlying matrix with entrywise complex conjugation,
and prove the normalized real trace is `C`-even.

No lattice, continuum, or spectral assumption is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Charge conjugation on `SU(N)`, written as transpose of the inverse.  For unitary matrices this
is exactly entrywise complex conjugation. -/
def specialUnitaryChargeConjugation
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.specialUnitaryGroup (Fin N) ℂ := by
  refine ⟨Matrix.transpose
      (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)), ?_⟩
  constructor
  · exact Matrix.transpose_mem_unitaryGroup_iff.mpr (U⁻¹).2.1
  · simpa using (U⁻¹).2.2

@[simp]
theorem specialUnitaryChargeConjugation_coe
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (specialUnitaryChargeConjugation U : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.transpose
        (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)) :=
  rfl

/-- On underlying matrices, charge conjugation is entrywise complex conjugation. -/
theorem specialUnitaryChargeConjugation_coe_eq_map_star
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (specialUnitaryChargeConjugation U : Matrix (Fin N) (Fin N) ℂ) =
      (U : Matrix (Fin N) (Fin N) ℂ).map star := by
  have hInv :
      (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)) =
        star (U : Matrix (Fin N) (Fin N) ℂ) := by
    rw [← Matrix.specialUnitaryGroup.coe_star]
    exact congrArg Subtype.val (Matrix.star_eq_inv U).symm
  rw [specialUnitaryChargeConjugation_coe, hInv,
    Matrix.star_eq_conjTranspose]
  ext i j
  rfl

/-- Charge conjugation is involutive. -/
@[simp]
theorem specialUnitaryChargeConjugation_involutive
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryChargeConjugation (specialUnitaryChargeConjugation U) = U := by
  apply Subtype.ext
  rw [specialUnitaryChargeConjugation_coe_eq_map_star,
    specialUnitaryChargeConjugation_coe_eq_map_star]
  ext i j
  simp

/-- Charge conjugation preserves multiplication. -/
@[simp]
theorem specialUnitaryChargeConjugation_mul
    {N : ℕ}
    (U V : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryChargeConjugation (U * V) =
      specialUnitaryChargeConjugation U * specialUnitaryChargeConjugation V := by
  apply Subtype.ext
  change
    (specialUnitaryChargeConjugation (U * V) :
      Matrix (Fin N) (Fin N) ℂ) =
      (specialUnitaryChargeConjugation U : Matrix (Fin N) (Fin N) ℂ) *
        (specialUnitaryChargeConjugation V : Matrix (Fin N) (Fin N) ℂ)
  rw [specialUnitaryChargeConjugation_coe_eq_map_star,
    specialUnitaryChargeConjugation_coe_eq_map_star,
    specialUnitaryChargeConjugation_coe_eq_map_star]
  ext i j
  simp [Matrix.mul_apply]

/-- Charge conjugation as a multiplicative equivalence of `SU(N)`. -/
def specialUnitaryChargeConjugationMulEquiv
    (N : ℕ) :
    Matrix.specialUnitaryGroup (Fin N) ℂ ≃*
      Matrix.specialUnitaryGroup (Fin N) ℂ where
  toFun := specialUnitaryChargeConjugation
  invFun := specialUnitaryChargeConjugation
  left_inv := specialUnitaryChargeConjugation_involutive
  right_inv := specialUnitaryChargeConjugation_involutive
  map_mul' := specialUnitaryChargeConjugation_mul

@[simp]
theorem specialUnitaryChargeConjugationMulEquiv_apply
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryChargeConjugationMulEquiv N U =
      specialUnitaryChargeConjugation U :=
  rfl

/-- Charge conjugation commutes with group inversion. -/
@[simp]
theorem specialUnitaryChargeConjugation_inv
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryChargeConjugation U⁻¹ =
      (specialUnitaryChargeConjugation U)⁻¹ := by
  exact (specialUnitaryChargeConjugationMulEquiv N).map_inv U

/-- The normalized real trace is charge-conjugation even. -/
theorem normalizedSpecialUnitaryRealTrace_chargeConjugation
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N (specialUnitaryChargeConjugation U) =
      normalizedSpecialUnitaryRealTrace N U := by
  calc
    normalizedSpecialUnitaryRealTrace N (specialUnitaryChargeConjugation U) =
        normalizedSpecialUnitaryRealTrace N U⁻¹ := by
      rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div,
        normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
      change
        (Matrix.trace
          (Matrix.transpose
            (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ)))).re / (N : ℝ) =
          (Matrix.trace
            (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ))).re / (N : ℝ)
      rw [Matrix.trace_transpose]
    _ = normalizedSpecialUnitaryRealTrace N U :=
      normalizedSpecialUnitaryRealTrace_inv U

end

end MathlibAnalytic
end MGAP4D
