import Mathlib.Analysis.Normed.Group.InfiniteSum
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ActualRayleighQuotient
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2InnerProductIdentification

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The actual diagonal operator has quadratic-form lower bound one on its whole
Mathlib `LinearPMap` domain. -/
theorem concrete_l2_r2_actual_energy_ge_norm_sq
    (x : concreteL2R2DenseDiagonalDomainLinearPMap.domain) :
    ‖(x : ConcreteL2R1HilbertCarrier)‖ ^ 2 ≤
      inner ℝ
        (concreteL2R2DenseDiagonalDomainLinearPMap x)
        (x : ConcreteL2R1HilbertCarrier) := by
  let xv : ConcreteL2R1HilbertCarrier :=
    (x : ConcreteL2R1HilbertCarrier)
  let Tx : ConcreteL2R1HilbertCarrier :=
    concreteL2R2DenseDiagonalDomainLinearPMap x
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    norm_num [Real.HolderConjugate]
  have hxNormSummable :
      Summable fun n : ℕ => ‖xv n‖ * ‖xv n‖ :=
    lp.summable_mul hholder xv xv
  have hxSummable :
      Summable fun n : ℕ => xv n * xv n := by
    apply Summable.of_norm
    simpa [norm_mul] using hxNormSummable
  have hTxNormSummable :
      Summable fun n : ℕ => ‖Tx n‖ * ‖xv n‖ :=
    lp.summable_mul hholder Tx xv
  have hTxSummable :
      Summable fun n : ℕ => Tx n * xv n := by
    apply Summable.of_norm
    simpa [norm_mul] using hTxNormSummable
  have hcoord : ∀ n : ℕ,
      Tx n = concreteL2R2DiagonalWeight n * xv n := by
    intro n
    dsimp [Tx, xv]
    rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_apply]
    rw [concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord]
    rfl
  have hpoint : ∀ n : ℕ,
      xv n * xv n ≤ Tx n * xv n := by
    intro n
    rw [hcoord n]
    have hweight := concrete_l2_r2_diagonal_weight_ge_one n
    have hsquare : 0 ≤ xv n * xv n := mul_self_nonneg (xv n)
    nlinarith
  have hsum :
      (∑' n : ℕ, xv n * xv n) ≤
        ∑' n : ℕ, Tx n * xv n :=
    hxSummable.tsum_le_tsum hpoint hTxSummable
  calc
    ‖(x : ConcreteL2R1HilbertCarrier)‖ ^ 2
        = inner ℝ xv xv := by
            simpa [xv] using
              (real_inner_self_eq_norm_sq xv).symm
    _ = concreteL2R2CoordinateTsumPairing xv xv :=
      concrete_l2_r2_inner_eq_coordinate_tsum_pairing xv xv
    _ = ∑' n : ℕ, xv n * xv n := rfl
    _ ≤ ∑' n : ℕ, Tx n * xv n := hsum
    _ = concreteL2R2CoordinateTsumPairing Tx xv := rfl
    _ = inner ℝ Tx xv :=
      (concrete_l2_r2_inner_eq_coordinate_tsum_pairing Tx xv).symm
    _ = inner ℝ
          (concreteL2R2DenseDiagonalDomainLinearPMap x)
          (x : ConcreteL2R1HilbertCarrier) := by
      rfl

/-- Every nonzero domain vector has Rayleigh quotient at least one. -/
theorem concrete_l2_r2_actual_rayleigh_quotient_ge_one
    (x : concreteL2R2DenseDiagonalDomainLinearPMap.domain)
    (hx : x ≠ 0) :
    1 ≤ concreteL2R2ActualRayleighQuotient x := by
  have hxCoe : (x : ConcreteL2R1HilbertCarrier) ≠ 0 := by
    intro hzero
    apply hx
    apply Subtype.ext
    exact hzero
  have hden : 0 < ‖(x : ConcreteL2R1HilbertCarrier)‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hxCoe)
  unfold concreteL2R2ActualRayleighQuotient
  apply (le_div_iff₀ hden).2
  simpa using concrete_l2_r2_actual_energy_ge_norm_sq x

/-- Rayleigh values of all nonzero vectors in the actual operator domain. -/
def concreteL2R2ActualNonzeroRayleighSet : Set ℝ :=
  {r : ℝ |
    ∃ x : concreteL2R2DenseDiagonalDomainLinearPMap.domain,
      x ≠ 0 ∧ concreteL2R2ActualRayleighQuotient x = r}

/-- The value one belongs to the full nonzero-domain Rayleigh set. -/
theorem concrete_l2_r2_one_mem_actual_nonzero_rayleigh_set :
    (1 : ℝ) ∈ concreteL2R2ActualNonzeroRayleighSet := by
  refine ⟨
    concreteL2R2CoordinateUnitDomainElement 0,
    concrete_l2_r2_coordinate_unit_domain_element_ne_zero 0,
    concrete_l2_r2_actual_rayleigh_quotient_zero_eq_one⟩

/-- Every Rayleigh value of a nonzero domain vector is at least one. -/
theorem concrete_l2_r2_actual_nonzero_rayleigh_set_lower_bound
    {r : ℝ}
    (hr : r ∈ concreteL2R2ActualNonzeroRayleighSet) :
    1 ≤ r := by
  rcases hr with ⟨x, hx, rfl⟩
  exact concrete_l2_r2_actual_rayleigh_quotient_ge_one x hx

/-- One is the least Rayleigh value on the entire nonzero operator domain. -/
theorem concrete_l2_r2_actual_nonzero_rayleigh_set_isLeast_one :
    IsLeast concreteL2R2ActualNonzeroRayleighSet (1 : ℝ) := by
  exact ⟨
    concrete_l2_r2_one_mem_actual_nonzero_rayleigh_set,
    fun _ hr => concrete_l2_r2_actual_nonzero_rayleigh_set_lower_bound hr⟩

/-- The variational infimum over all nonzero domain vectors is exactly one. -/
theorem concrete_l2_r2_actual_nonzero_rayleigh_set_sInf_eq_one :
    sInf concreteL2R2ActualNonzeroRayleighSet = (1 : ℝ) := by
  have hBdd : BddBelow concreteL2R2ActualNonzeroRayleighSet :=
    ⟨1, fun _ hr => concrete_l2_r2_actual_nonzero_rayleigh_set_lower_bound hr⟩
  have hNonempty : concreteL2R2ActualNonzeroRayleighSet.Nonempty :=
    ⟨1, concrete_l2_r2_one_mem_actual_nonzero_rayleigh_set⟩
  apply le_antisymm
  · exact csInf_le hBdd concrete_l2_r2_one_mem_actual_nonzero_rayleigh_set
  · exact le_csInf hNonempty
      (fun _ hr => concrete_l2_r2_actual_nonzero_rayleigh_set_lower_bound hr)

/-- The coordinate-unit Rayleigh set is contained in the full nonzero-domain
Rayleigh set. -/
theorem concrete_l2_r2_coordinate_unit_rayleigh_set_subset_actual_nonzero :
    concreteL2R2CoordinateUnitRayleighSet ⊆
      concreteL2R2ActualNonzeroRayleighSet := by
  intro r hr
  rcases hr with ⟨n, rfl⟩
  exact ⟨
    concreteL2R2CoordinateUnitDomainElement n,
    concrete_l2_r2_coordinate_unit_domain_element_ne_zero n,
    rfl⟩

/-- The actual self-adjoint diagonal operator has global Rayleigh lower edge one,
attained at the zeroth coordinate unit. -/
theorem concrete_l2_r2_self_adjoint_diagonal_global_rayleigh_lower_edge_one :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
    (∀ x : concreteL2R2DenseDiagonalDomainLinearPMap.domain,
      x ≠ 0 → 1 ≤ concreteL2R2ActualRayleighQuotient x) ∧
    IsLeast concreteL2R2ActualNonzeroRayleighSet (1 : ℝ) ∧
    sInf concreteL2R2ActualNonzeroRayleighSet = (1 : ℝ) ∧
    concreteL2R2ActualRayleighQuotient
      (concreteL2R2CoordinateUnitDomainElement 0) = (1 : ℝ) := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_actual_rayleigh_quotient_ge_one,
    concrete_l2_r2_actual_nonzero_rayleigh_set_isLeast_one,
    concrete_l2_r2_actual_nonzero_rayleigh_set_sInf_eq_one,
    concrete_l2_r2_actual_rayleigh_quotient_zero_eq_one⟩

end

end MathlibAnalytic
end MGAP4D
