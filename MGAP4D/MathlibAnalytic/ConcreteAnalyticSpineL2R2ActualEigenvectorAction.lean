import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalPointSpectrumLowerBound
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateUnitsInDomain

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The `n`th coordinate unit, bundled as an element of the actual Mathlib
`LinearPMap` domain. -/
def concreteL2R2CoordinateUnitDomainElement
    (n : ℕ) : concreteL2R2DenseDiagonalDomainLinearPMap.domain :=
  ⟨concreteL2MathlibUnit n, by
    rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain]
    exact concrete_l2_r2_diagonal_domain_candidate_mathlib_unit n⟩

@[simp] theorem concrete_l2_r2_coordinate_unit_domain_element_val
    (n : ℕ) :
    (concreteL2R2CoordinateUnitDomainElement n : ConcreteL2R1HilbertCarrier) =
      concreteL2MathlibUnit n := by
  rfl

/-- The actual partially-defined diagonal operator acts on the `n`th coordinate
unit by multiplication with the diagonal weight `n + 1`. -/
theorem concrete_l2_r2_actual_linear_pmap_apply_coordinate_unit
    (n : ℕ) :
    concreteL2R2DenseDiagonalDomainLinearPMap
        (concreteL2R2CoordinateUnitDomainElement n) =
      concreteL2R2DiagonalWeight n • concreteL2MathlibUnit n := by
  apply concrete_l2_r2_completed_l2_ext
  intro m
  rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_apply]
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord]
  change concreteL2R2DiagonalWeight m * concreteL2MathlibUnit n m =
    (concreteL2R2DiagonalWeight n • concreteL2MathlibUnit n) m
  by_cases h : m = n
  · subst m
    simp [concrete_l2_mathlib_unit_apply_self]
  · have hunit : concreteL2MathlibUnit n m = 0 :=
      concrete_l2_mathlib_unit_apply_ne h
    simp [hunit]

/-- The bundled coordinate unit is nonzero. -/
theorem concrete_l2_r2_coordinate_unit_domain_element_ne_zero
    (n : ℕ) :
    concreteL2R2CoordinateUnitDomainElement n ≠ 0 := by
  intro hzero
  have hval : concreteL2MathlibUnit n = 0 := by
    exact congrArg
      (fun x : concreteL2R2DenseDiagonalDomainLinearPMap.domain =>
        (x : ConcreteL2R1HilbertCarrier)) hzero
  have hnorm : ‖concreteL2MathlibUnit n‖ = 0 := by
    rw [hval]
    simp
  rw [concrete_l2_mathlib_unit_norm_eq_one] at hnorm
  norm_num at hnorm

/-- Every diagonal weight is an actual eigenvalue of the Mathlib `LinearPMap`,
with a nonzero domain eigenvector. -/
theorem concrete_l2_r2_actual_linear_pmap_has_coordinate_eigenvector
    (n : ℕ) :
    ∃ x : concreteL2R2DenseDiagonalDomainLinearPMap.domain,
      x ≠ 0 ∧
      concreteL2R2DenseDiagonalDomainLinearPMap x =
        concreteL2R2DiagonalWeight n •
          (x : ConcreteL2R1HilbertCarrier) := by
  refine ⟨concreteL2R2CoordinateUnitDomainElement n,
    concrete_l2_r2_coordinate_unit_domain_element_ne_zero n, ?_⟩
  simpa using concrete_l2_r2_actual_linear_pmap_apply_coordinate_unit n

/-- The lower-edge eigenvalue one is realized by an actual nonzero eigenvector
of the self-adjoint Mathlib `LinearPMap`. -/
theorem concrete_l2_r2_actual_linear_pmap_has_eigenvalue_one :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
    ∃ x : concreteL2R2DenseDiagonalDomainLinearPMap.domain,
      x ≠ 0 ∧
      concreteL2R2DenseDiagonalDomainLinearPMap x =
        (1 : ℝ) • (x : ConcreteL2R1HilbertCarrier) := by
  refine ⟨concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint, ?_⟩
  rcases concrete_l2_r2_actual_linear_pmap_has_coordinate_eigenvector 0 with
    ⟨x, hxNonzero, hxEig⟩
  refine ⟨x, hxNonzero, ?_⟩
  simpa [concrete_l2_r2_diagonal_weight_zero_eq_one] using hxEig

/-- The explicit point-spectrum candidate is realized pointwise by actual
nonzero eigenvectors of the self-adjoint Mathlib operator. -/
theorem concrete_l2_r2_diagonal_point_spectrum_realized_by_actual_eigenvectors
    {lam : ℝ}
    (hlam : lam ∈ concreteL2R2DiagonalPointSpectrum) :
    ∃ x : concreteL2R2DenseDiagonalDomainLinearPMap.domain,
      x ≠ 0 ∧
      concreteL2R2DenseDiagonalDomainLinearPMap x =
        lam • (x : ConcreteL2R1HilbertCarrier) := by
  rcases hlam with ⟨n, rfl⟩
  exact concrete_l2_r2_actual_linear_pmap_has_coordinate_eigenvector n

end

end MathlibAnalytic
end MGAP4D
