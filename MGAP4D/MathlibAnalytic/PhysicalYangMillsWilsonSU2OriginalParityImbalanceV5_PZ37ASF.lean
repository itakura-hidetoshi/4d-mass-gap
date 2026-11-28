import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSystematicParityCoordinatesV5_PZ37ASE
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ASF — degree-dependent parity imbalance

The alternating binomial multiplicities of the actual symmetric local
indices have imbalance at most the last binomial coefficient. Prove the
two parity cases by induction and retain the exact coefficient identity.
The systematic ASE upper bound then yields a denominator-free relative
suppression inequality, with the genuine lattice dimensions. This does
not bound the absolute spectral count uniformly in volume.
-/
namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

local notation "F" => ZMod 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink
local notation "Mlt" => p4Q2PZ37ASB_localMultiplicity
local notation "MaxM" => p4Q2PZ37ASC_maxMultiplicity
local notation "S" => p4Q2PZ37ARX_localTerms
local notation "Rank" => p4Q2PZ37ASC_boundaryRank
local notation "Dim" => p4Q2PZ37ASC_cycleDim

/-- Highest-degree binomial multiplicity of the literal eight-coordinate index. -/
def p4Q2PZ37ASF_degreeWeight (m : ℕ) : ℕ :=
  (m+7).choose 7

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_degreeWeight

local notation "A" => p4Q2PZ37ASF_degreeWeight

theorem p4Q2PZ37ASF_range_formula (m : ℕ) (p : F) :
    Mlt m p = ∑ k ∈ Finset.range (m+1), if (k : F) = p then A k else 0 := by
  classical
  rw [p4Q2PZ37ASC_localMultiplicity_formula, Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if (k : F) = p then A k else 0) (m+1)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_range_formula

theorem p4Q2PZ37ASF_step (m : ℕ) (p : F) :
    Mlt (m+1) p = Mlt m p + if ((m+1 : ℕ) : F) = p then A (m+1) else 0 := by
  rw [p4Q2PZ37ASF_range_formula (m+1) p, p4Q2PZ37ASF_range_formula m p,
    Finset.sum_range_succ]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_step

theorem p4Q2PZ37ASF_degree_mono (m : ℕ) : A m ≤ A (m+1) := by
  unfold p4Q2PZ37ASF_degreeWeight
  exact Nat.choose_le_choose 7 (by omega)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_degree_mono

private theorem p4Q2PZ37ASF_zero_even : Mlt 0 0 = 1 := by
  rw [p4Q2PZ37ASF_range_formula]
  decide

private theorem p4Q2PZ37ASF_zero_odd : Mlt 0 1 = 0 := by
  rw [p4Q2PZ37ASF_range_formula]
  decide

private theorem p4Q2PZ37ASF_even_step (m : ℕ) (h : Even (m+1)) :
    Mlt (m+1) 0 = Mlt m 0 + A (m+1) ∧ Mlt (m+1) 1 = Mlt m 1 := by
  have hz := ZMod.natCast_eq_zero_iff_even.mpr h
  constructor
  · rw [p4Q2PZ37ASF_step, hz, if_pos rfl]
  · rw [p4Q2PZ37ASF_step, hz, if_neg (by decide : (0 : F) ≠ 1), add_zero]

private theorem p4Q2PZ37ASF_odd_step (m : ℕ) (h : Odd (m+1)) :
    Mlt (m+1) 1 = Mlt m 1 + A (m+1) ∧ Mlt (m+1) 0 = Mlt m 0 := by
  have hz := ZMod.natCast_eq_one_iff_odd.mpr h
  constructor
  · rw [p4Q2PZ37ASF_step, hz, if_pos rfl]
  · rw [p4Q2PZ37ASF_step, hz, if_neg (by decide : (1 : F) ≠ 0), add_zero]

/-- The last degree determines the dominant parity, and bounds the imbalance. -/
theorem p4Q2PZ37ASF_balance (m : ℕ) :
    (Even m → Mlt m 1 ≤ Mlt m 0 ∧ Mlt m 0 ≤ Mlt m 1 + A m) ∧
    (Odd m → Mlt m 0 ≤ Mlt m 1 ∧ Mlt m 1 ≤ Mlt m 0 + A m) := by
  induction m with
  | zero =>
    rw [p4Q2PZ37ASF_zero_even, p4Q2PZ37ASF_zero_odd]
    decide
  | succ m ih =>
    have hm := p4Q2PZ37ASF_degree_mono m
    constructor
    · intro he
      have ho : Odd m := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)
      obtain ⟨h1,h2⟩ := ih.2 ho
      obtain ⟨h3,h4⟩ := p4Q2PZ37ASF_even_step m he
      rw [h3,h4]
      constructor <;> omega
    · intro ho
      have he : Even m := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp ho)
      obtain ⟨h1,h2⟩ := ih.1 he
      obtain ⟨h3,h4⟩ := p4Q2PZ37ASF_odd_step m ho
      rw [h3,h4]
      constructor <;> omega

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_balance

theorem p4Q2PZ37ASF_imbalance (m : ℕ) :
    Mlt m 0 ≤ Mlt m 1 + A m ∧ Mlt m 1 ≤ Mlt m 0 + A m := by
  obtain ⟨he,ho⟩ := p4Q2PZ37ASF_balance m
  by_cases h : Even m
  · obtain ⟨h1,h2⟩ := he h
    omega
  · obtain ⟨h1,h2⟩ := ho (Nat.not_even_iff_odd.mp h)
    omega

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_imbalance

/-- Exact ratio identity for the terminal multiplicity and total local terms. -/
theorem p4Q2PZ37ASF_degree_total (m : ℕ) :
    (m+8)*A m = 8*S m := by
  unfold p4Q2PZ37ASF_degreeWeight p4Q2PZ37ARX_localTerms
  calc
    _ = (m+8).choose 8 * 8 := Nat.add_one_mul_choose_eq (m+7) 7
    _ = _ := Nat.mul_comm _ _

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_degree_total

theorem p4Q2PZ37ASF_total_pos (m : ℕ) : 0 < S m := by
  unfold p4Q2PZ37ARX_localTerms
  exact Nat.choose_pos (by omega)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_total_pos

theorem p4Q2PZ37ASF_max_le (m : ℕ) :
    2*MaxM m ≤ S m + A m := by
  obtain ⟨h0,h1⟩ := p4Q2PZ37ASF_imbalance m
  have ht := p4Q2PZ37ASC_localMultiplicity_total m
  unfold p4Q2PZ37ASC_maxMultiplicity
  rcases le_total (Mlt m 0) (Mlt m 1) with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_max_le

/-- The upper probability of either local parity is at most (m+16)/(2(m+8)). -/
theorem p4Q2PZ37ASF_scaled_max (m : ℕ) :
    (2*(m+8))*MaxM m ≤ (m+16)*S m := by
  calc
    _ = (m+8)*(2*MaxM m) := by ring
    _ ≤ (m+8)*(S m+A m) := Nat.mul_le_mul_left _ (p4Q2PZ37ASF_max_le m)
    _ = _ := by
      rw [Nat.mul_add, p4Q2PZ37ASF_degree_total]
      ring

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_scaled_max

/-- Relative suppression of the literal weighted survivor count, with no division. -/
theorem p4Q2PZ37ASF_scaled_survivors (H m : ℕ) :
    (2*(m+8))^(Rank H) * (p4Q2PZ37ASB_survivors H m).card ≤
      (m+16)^(Rank H) * (S m)^(Nat.card (Link H)) := by
  have h := p4Q2PZ37ASE_survivors_le_systematic H m
  rw [p4Q2PZ37ASC_localMultiplicity_total] at h
  calc
    _ ≤ (2*(m+8))^(Rank H) * ((MaxM m)^(Rank H)*(S m)^(Dim H)) :=
      Nat.mul_le_mul_left _ h
    _ = ((2*(m+8))*MaxM m)^(Rank H) * (S m)^(Dim H) := by
      rw [mul_pow (2*(m+8)) (MaxM m)]
      ac_rfl
    _ ≤ ((m+16)*S m)^(Rank H)*(S m)^(Dim H) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (p4Q2PZ37ASF_scaled_max m) _)
    _ = _ := by
      rw [mul_pow (m+16) (S m), ← p4Q2PZ37ASC_rank_nullity H, pow_add]
      exact mul_assoc _ _ _

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_scaled_survivors

theorem p4Q2PZ37ASF_scaled_survivors_numeric (H m : ℕ) :
    (2*(m+8))^(8*(H+1)^3-1) * (p4Q2PZ37ASB_survivors H m).card ≤
      (m+16)^(8*(H+1)^3-1) * (S m)^(24*(H+1)^3) := by
  simpa only [p4Q2PZ37ASD_rank_numeric, p4Q2PZ37ASD_link_card] using
    p4Q2PZ37ASF_scaled_survivors H m

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASF_scaled_survivors_numeric

end
end MGAP4D.MathlibAnalytic
