import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ActualEigenvectorAction
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AdjointGraphCandidateStructure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Rayleigh quotient of the actual dense-domain diagonal `LinearPMap`. -/
def concreteL2R2ActualRayleighQuotient
    (x : concreteL2R2DenseDiagonalDomainLinearPMap.domain) : ℝ :=
  inner ℝ
      (concreteL2R2DenseDiagonalDomainLinearPMap x)
      (x : ConcreteL2R1HilbertCarrier) /
    ‖(x : ConcreteL2R1HilbertCarrier)‖ ^ 2

/-- The energy expectation of the `n`th coordinate unit is exactly the diagonal
weight `n + 1`. -/
theorem concrete_l2_r2_coordinate_unit_energy_expectation
    (n : ℕ) :
    inner ℝ
        (concreteL2R2DenseDiagonalDomainLinearPMap
          (concreteL2R2CoordinateUnitDomainElement n))
        (concreteL2R2CoordinateUnitDomainElement n : ConcreteL2R1HilbertCarrier) =
      concreteL2R2DiagonalWeight n := by
  rw [concrete_l2_r2_actual_linear_pmap_apply_coordinate_unit]
  rw [real_inner_smul_left]
  rw [concrete_l2_r2_inner_mathlib_unit_eq_coordinate]
  rw [concrete_l2_mathlib_unit_apply_self]
  ring

/-- The Rayleigh quotient at the `n`th coordinate unit is exactly `n + 1`. -/
theorem concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit
    (n : ℕ) :
    concreteL2R2ActualRayleighQuotient
        (concreteL2R2CoordinateUnitDomainElement n) =
      concreteL2R2DiagonalWeight n := by
  unfold concreteL2R2ActualRayleighQuotient
  rw [concrete_l2_r2_coordinate_unit_energy_expectation]
  have hnorm :
      ‖(concreteL2R2CoordinateUnitDomainElement n : ConcreteL2R1HilbertCarrier)‖ = 1 := by
    simpa using concrete_l2_mathlib_unit_norm_eq_one n
  rw [hnorm]
  norm_num

/-- Every coordinate-unit Rayleigh quotient is bounded below by one. -/
theorem concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit_ge_one
    (n : ℕ) :
    1 ≤ concreteL2R2ActualRayleighQuotient
      (concreteL2R2CoordinateUnitDomainElement n) := by
  rw [concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit]
  exact concrete_l2_r2_diagonal_weight_ge_one n

/-- The lower-edge Rayleigh quotient is attained at the zeroth coordinate unit. -/
theorem concrete_l2_r2_actual_rayleigh_quotient_zero_eq_one :
    concreteL2R2ActualRayleighQuotient
      (concreteL2R2CoordinateUnitDomainElement 0) = (1 : ℝ) := by
  rw [concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit]
  exact concrete_l2_r2_diagonal_weight_zero_eq_one

/-- The coordinate-unit Rayleigh quotient set. -/
def concreteL2R2CoordinateUnitRayleighSet : Set ℝ :=
  Set.range
    (fun n : ℕ =>
      concreteL2R2ActualRayleighQuotient
        (concreteL2R2CoordinateUnitDomainElement n))

/-- The coordinate-unit Rayleigh quotient set is exactly the explicit diagonal
point-spectrum candidate.  Thus the variational values on the canonical
orthonormal coordinate family coincide pointwise with the actual eigenvalues
constructed earlier. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum :
    concreteL2R2CoordinateUnitRayleighSet = concreteL2R2DiagonalPointSpectrum := by
  ext lam
  constructor
  · intro hlam
    rcases hlam with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    exact concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit n
  · intro hlam
    rcases hlam with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    exact (concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit n).symm

/-- One belongs to the coordinate-unit Rayleigh quotient set. -/
theorem concrete_l2_r2_one_mem_coordinate_unit_rayleigh_set :
    (1 : ℝ) ∈ concreteL2R2CoordinateUnitRayleighSet := by
  rw [concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum]
  exact concrete_l2_r2_one_mem_diagonal_point_spectrum

/-- Every coordinate-unit Rayleigh quotient is at least one. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_lower_bound
    {r : ℝ}
    (hr : r ∈ concreteL2R2CoordinateUnitRayleighSet) :
    1 ≤ r := by
  rw [concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum] at hr
  exact concrete_l2_r2_diagonal_point_spectrum_lower_bound hr

/-- The coordinate-unit Rayleigh quotient set has least element one. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_isLeast_one :
    IsLeast concreteL2R2CoordinateUnitRayleighSet (1 : ℝ) := by
  rw [concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum]
  exact concrete_l2_r2_diagonal_point_spectrum_isLeast_one

/-- The infimum of the coordinate-unit Rayleigh quotient set is exactly one. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_sInf_eq_one :
    sInf concreteL2R2CoordinateUnitRayleighSet = (1 : ℝ) := by
  rw [concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum]
  exact concrete_l2_r2_diagonal_point_spectrum_sInf_eq_one

/-- The nonzero coordinate-unit Rayleigh values have the same exact lower edge. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_nonzero_sInf_eq_one :
    sInf (concreteL2R2CoordinateUnitRayleighSet \ ({0} : Set ℝ)) = (1 : ℝ) := by
  rw [concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum]
  exact concrete_l2_r2_diagonal_nonzero_point_spectrum_sInf_eq_one

/-- Every coordinate-unit Rayleigh value is realized by an actual nonzero
eigenvector of the self-adjoint operator. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_value_realized_by_actual_eigenvector
    {r : ℝ}
    (hr : r ∈ concreteL2R2CoordinateUnitRayleighSet) :
    ∃ x : concreteL2R2DenseDiagonalDomainLinearPMap.domain,
      x ≠ 0 ∧
      concreteL2R2DenseDiagonalDomainLinearPMap x =
        r • (x : ConcreteL2R1HilbertCarrier) := by
  rw [concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum] at hr
  exact concrete_l2_r2_diagonal_point_spectrum_realized_by_actual_eigenvectors hr

/-- The actual self-adjoint diagonal operator realizes the lower-edge value one
both as an eigenvalue and as an attained Rayleigh quotient, and the canonical
Rayleigh set coincides exactly with the explicit point spectrum. -/
theorem concrete_l2_r2_self_adjoint_diagonal_attains_rayleigh_lower_edge_one :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
    concreteL2R2ActualRayleighQuotient
      (concreteL2R2CoordinateUnitDomainElement 0) = (1 : ℝ) ∧
    concreteL2R2CoordinateUnitRayleighSet = concreteL2R2DiagonalPointSpectrum ∧
    IsLeast concreteL2R2CoordinateUnitRayleighSet (1 : ℝ) ∧
    sInf concreteL2R2CoordinateUnitRayleighSet = (1 : ℝ) ∧
    sInf (concreteL2R2CoordinateUnitRayleighSet \ ({0} : Set ℝ)) = (1 : ℝ) := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_actual_rayleigh_quotient_zero_eq_one,
    concrete_l2_r2_coordinate_unit_rayleigh_set_eq_diagonal_point_spectrum,
    concrete_l2_r2_coordinate_unit_rayleigh_set_isLeast_one,
    concrete_l2_r2_coordinate_unit_rayleigh_set_sInf_eq_one,
    concrete_l2_r2_coordinate_unit_rayleigh_nonzero_sInf_eq_one⟩

end

end MathlibAnalytic
end MGAP4D
