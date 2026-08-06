import MGAP4D.MathlibAnalytic.FiniteDimensionalUniqueGroundCenteredRayleigh
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperatorLowerBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- The ground-lifted defect coefficient.  It equals one on the transfer-fixed
sector and equals the ordinary defect coefficient `1 - λ` on every other
spectral mode. -/
def groundLiftedDefectCoefficient (i : Fin D.dimension) : ℝ :=
  if D.eigenvalue i = 1 then 1 else 1 - D.eigenvalue i

/-- The transfer defect with the ground sector lifted from zero to one.

This bounded symmetric operator is diagonal in the canonical transfer
eigenbasis.  On the ground sector it is the identity; on every excited or null
mode it agrees with `I - T`.  It is therefore coercive on the full finite
Hilbert space whenever the ordinary transfer defect is uniformly coercive on
the ground-centered sector. -/
noncomputable def groundLiftedDefect : E →L[ℝ] E :=
  orthonormalDiagonalOperator D.eigenbasis D.groundLiftedDefectCoefficient

@[simp] theorem groundLiftedDefect_apply_eigenbasis
    (i : Fin D.dimension) :
    D.groundLiftedDefect (D.eigenbasis i) =
      D.groundLiftedDefectCoefficient i • D.eigenbasis i := by
  exact orthonormalDiagonalOperator_apply_basis
    D.eigenbasis D.groundLiftedDefectCoefficient i

/-- The ground-lifted defect is symmetric. -/
theorem groundLiftedDefect_isSymmetric :
    D.groundLiftedDefect.toLinearMap.IsSymmetric :=
  orthonormalDiagonalLinearMap_isSymmetric
    D.eigenbasis D.groundLiftedDefectCoefficient

/-- Every ground eigenmode receives coefficient one. -/
@[simp] theorem groundLiftedDefectCoefficient_ground
    (i : D.GroundSpectralIndex) :
    D.groundLiftedDefectCoefficient i.1 = 1 := by
  simp [groundLiftedDefectCoefficient, i.2]

/-- Every strictly excited eigenmode receives its ordinary defect coefficient. -/
@[simp] theorem groundLiftedDefectCoefficient_excited
    (i : D.ExcitedSpectralIndex) :
    D.groundLiftedDefectCoefficient i.1 = 1 - D.eigenvalue i.1 := by
  simp [groundLiftedDefectCoefficient, ne_of_lt i.2.2]

/-- Every null eigenmode receives coefficient one. -/
@[simp] theorem groundLiftedDefectCoefficient_null
    (i : D.NullSpectralIndex) :
    D.groundLiftedDefectCoefficient i.1 = 1 := by
  simp [groundLiftedDefectCoefficient, i.2]

/-- A common excited spectral cap `λ ≤ 1 - c`, together with `c ≤ 1`, gives a
pointwise coefficient lower bound `c` for the full ground-lifted defect. -/
theorem groundLiftedDefectCoefficient_ge_of_excited_cap
    (coercivity : ℝ)
    (hCoercivityLeOne : coercivity ≤ 1)
    (hExcited : ∀ i : D.ExcitedSpectralIndex,
      D.eigenvalue i.1 ≤ 1 - coercivity)
    (i : Fin D.dimension) :
    coercivity ≤ D.groundLiftedDefectCoefficient i := by
  rcases D.eigenvalue_trichotomy i with hNull | hExcitedMode | hGround
  · simp [groundLiftedDefectCoefficient, hNull, hCoercivityLeOne]
  · rw [D.groundLiftedDefectCoefficient_excited ⟨i, hExcitedMode⟩]
    linarith [hExcited ⟨i, hExcitedMode⟩]
  · simpa [D.groundLiftedDefectCoefficient_ground ⟨i, hGround⟩] using
      hCoercivityLeOne

/-- The common excited cap becomes a basis-free coercive quadratic lower bound
on the entire finite Hilbert space after lifting the ground sector. -/
theorem groundLiftedDefect_quadratic_lower_bound_of_excited_cap
    (coercivity : ℝ)
    (hCoercivityLeOne : coercivity ≤ 1)
    (hExcited : ∀ i : D.ExcitedSpectralIndex,
      D.eigenvalue i.1 ≤ 1 - coercivity)
    (x : E) :
    coercivity * ‖x‖ ^ 2 ≤ inner ℝ (D.groundLiftedDefect x) x := by
  exact orthonormalDiagonalOperator_quadratic_form_lower_bound
    D.eigenbasis D.groundLiftedDefectCoefficient coercivity
    (D.groundLiftedDefectCoefficient_ge_of_excited_cap
      coercivity hCoercivityLeOne hExcited) x

/-- On a ground eigenmode the lifted defect is exactly the identity. -/
theorem groundLiftedDefect_apply_ground
    (i : D.GroundSpectralIndex) :
    D.groundLiftedDefect (D.eigenbasis i.1) = D.eigenbasis i.1 := by
  rw [D.groundLiftedDefect_apply_eigenbasis]
  simp

/-- On a strictly excited eigenmode the lifted defect is exactly `I - T`. -/
theorem groundLiftedDefect_apply_excited
    (i : D.ExcitedSpectralIndex) :
    D.groundLiftedDefect (D.eigenbasis i.1) =
      D.eigenbasis i.1 - D.operator (D.eigenbasis i.1) := by
  rw [D.groundLiftedDefect_apply_eigenbasis,
    D.groundLiftedDefectCoefficient_excited,
    D.operator_apply_eigenbasis]
  module

/-- On a null eigenmode the lifted defect also agrees with `I - T`, hence is
the identity. -/
theorem groundLiftedDefect_apply_null
    (i : D.NullSpectralIndex) :
    D.groundLiftedDefect (D.eigenbasis i.1) =
      D.eigenbasis i.1 - D.operator (D.eigenbasis i.1) := by
  rw [D.groundLiftedDefect_apply_eigenbasis,
    D.groundLiftedDefectCoefficient_null,
    D.operator_apply_eigenbasis, i.2]
  simp

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
