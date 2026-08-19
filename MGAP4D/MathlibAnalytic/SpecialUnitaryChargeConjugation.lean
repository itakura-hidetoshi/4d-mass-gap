import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedRealTraceInversion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Charge conjugation on `SU(N)`

For a unitary matrix, entrywise complex conjugation is equivalently the transpose of its inverse.
We therefore define the finite-Wilson charge-conjugation involution by

`C(U) = (U⁻¹)ᵀ`.

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
  refine ⟨(((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ))ᵀ, ?_⟩
  constructor
  · exact Matrix.transpose_mem_unitaryGroup_iff.mpr (U⁻¹).2.1
  · simpa using (U⁻¹).2.2

@[simp]
theorem specialUnitaryChargeConjugation_coe
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (specialUnitaryChargeConjugation U : Matrix (Fin N) (Fin N) ℂ) =
      (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))ᵀ :=
  rfl

/-- On underlying matrices, charge conjugation is entrywise complex conjugation. -/
theorem specialUnitaryChargeConjugation_coe_eq_map_star
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (specialUnitaryChargeConjugation U : Matrix (Fin N) (Fin N) ℂ) =
      (U : Matrix (Fin N) (Fin N) ℂ).map star := by
  ext i j
  simp [specialUnitaryChargeConjugation, Matrix.specialUnitaryGroup.coe_star,
    Matrix.star_eq_conjTranspose]

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
  rw [specialUnitaryChargeConjugation_coe_eq_map_star,
    specialUnitaryChargeConjugation_coe_eq_map_star,
    specialUnitaryChargeConjugation_coe_eq_map_star]
  ext i j
  simp [Matrix.mul_apply, Finset.star_sum]

/-- Charge conjugation commutes with group inversion. -/
@[simp]
theorem specialUnitaryChargeConjugation_inv
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryChargeConjugation U⁻¹ =
      (specialUnitaryChargeConjugation U)⁻¹ := by
  apply inv_injective
  rw [inv_inv, ← specialUnitaryChargeConjugation_mul]
  simp

/-- The normalized real trace is charge-conjugation even. -/
theorem normalizedSpecialUnitaryRealTrace_chargeConjugation
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N (specialUnitaryChargeConjugation U) =
      normalizedSpecialUnitaryRealTrace N U := by
  rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div,
    normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
  rw [specialUnitaryChargeConjugation_coe]
  rw [Matrix.trace_transpose]
  have hInv := normalizedSpecialUnitaryRealTrace_inv U
  rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div,
    normalizedSpecialUnitaryRealTrace_eq_trace_re_div] at hInv
  exact hInv

end

end MathlibAnalytic
end MGAP4D
