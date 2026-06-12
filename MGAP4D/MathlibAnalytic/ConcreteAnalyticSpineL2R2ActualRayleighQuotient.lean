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

/-- The coordinate-unit Rayleigh quotient set has least element one. -/
def concreteL2R2CoordinateUnitRayleighSet : Set ℝ :=
  Set.range
    (fun n : ℕ =>
      concreteL2R2ActualRayleighQuotient
        (concreteL2R2CoordinateUnitDomainElement n))

/-- One belongs to the coordinate-unit Rayleigh quotient set. -/
theorem concrete_l2_r2_one_mem_coordinate_unit_rayleigh_set :
    (1 : ℝ) ∈ concreteL2R2CoordinateUnitRayleighSet := by
  refine ⟨0, ?_⟩
  exact concrete_l2_r2_actual_rayleigh_quotient_zero_eq_one

/-- Every coordinate-unit Rayleigh quotient is at least one. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_lower_bound
    {r : ℝ}
    (hr : r ∈ concreteL2R2CoordinateUnitRayleighSet) :
    1 ≤ r := by
  rcases hr with ⟨n, rfl⟩
  exact concrete_l2_r2_actual_rayleigh_quotient_coordinate_unit_ge_one n

/-- The coordinate-unit Rayleigh quotient set has least element one. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_isLeast_one :
    IsLeast concreteL2R2CoordinateUnitRayleighSet (1 : ℝ) := by
  exact ⟨
    concrete_l2_r2_one_mem_coordinate_unit_rayleigh_set,
    fun _ hr => concrete_l2_r2_coordinate_unit_rayleigh_set_lower_bound hr⟩

/-- The infimum of the coordinate-unit Rayleigh quotient set is exactly one. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_sInf_eq_one :
    sInf concreteL2R2CoordinateUnitRayleighSet = (1 : ℝ) := by
  have hBdd : BddBelow concreteL2R2CoordinateUnitRayleighSet :=
    ⟨1, fun _ hr => concrete_l2_r2_coordinate_unit_rayleigh_set_lower_bound hr⟩
  have hNonempty : concreteL2R2CoordinateUnitRayleighSet.Nonempty :=
    ⟨1, concrete_l2_r2_one_mem_coordinate_unit_rayleigh_set⟩
  apply le_antisymm
  · exact csInf_le hBdd concrete_l2_r2_one_mem_coordinate_unit_rayleigh_set
  · exact le_csInf hNonempty
      (fun _ hr => concrete_l2_r2_coordinate_unit_rayleigh_set_lower_bound hr)

/-- The actual self-adjoint diagonal operator realizes the lower-edge value one
both as an eigenvalue and as an attained Rayleigh quotient. -/
theorem concrete_l2_r2_self_adjoint_diagonal_attains_rayleigh_lower_edge_one :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
    concreteL2R2ActualRayleighQuotient
      (concreteL2R2CoordinateUnitDomainElement 0) = (1 : ℝ) ∧
    IsLeast concreteL2R2CoordinateUnitRayleighSet (1 : ℝ) ∧
    sInf concreteL2R2CoordinateUnitRayleighSet = (1 : ℝ) := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_actual_rayleigh_quotient_zero_eq_one,
    concrete_l2_r2_coordinate_unit_rayleigh_set_isLeast_one,
    concrete_l2_r2_coordinate_unit_rayleigh_set_sInf_eq_one⟩

end

end MathlibAnalytic
end MGAP4D
