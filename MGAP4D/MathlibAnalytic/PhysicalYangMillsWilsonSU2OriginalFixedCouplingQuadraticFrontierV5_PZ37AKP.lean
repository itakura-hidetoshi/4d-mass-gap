import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuadraticAJANoGoThroughThirteenV5_PZ37AKO
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKP: exact fixed-beta0 frontier of the AKN quadratic test

Retain the original Wilson SU2 source/operator/halfweight/Haar/margin.
AKN's sufficient no-witness criterion is
  beta0^2 * p_H / 2 <= log 4.
AKO certifies it for H<=13. We prove the converse, i.e., that for H>=14
the exact unchanged beta0 violates this *scalar test*. This does NOT
prove an AJA finite-power witness for H>=14.

The lower estimate log(3/2)>=3/8 follows from three original-log
telescoping factors (7/6)*(8/7)*(9/8)=3/2 and the universal
  1-x^(-1) <= log x.
Then beta0>=3/512. Since p_H>=81000 for H>=14,
  beta0^2*p_H/2 >= 81000*(3/512)^2/2 = 91125/65536 > 139/100.
Pinned Mathlib log_two_lt_d9 gives log4<139/100.
Therefore the exact original fixed-beta0 quadratic test holds if and
only if H<=13, and its loss of applicability at H>=14 must be recorded
as an obstruction, not promoted to an existence claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Telescoping logarithms and the rational lower tangent certify an
unconditional lower bound on the original fixed-coupling numerator. -/
theorem p4Q2PZ37AKP_threeEighths_le_log_threeHalves :
    (3 / 8 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
  have h7 : (1 / 7 : ℝ) ≤ Real.log (7 / 6 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < (7 / 6 : ℝ) by norm_num)
    norm_num at h
    exact h
  have h8 : (1 / 8 : ℝ) ≤ Real.log (8 / 7 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < (8 / 7 : ℝ) by norm_num)
    norm_num at h
    exact h
  have h9 : (1 / 9 : ℝ) ≤ Real.log (9 / 8 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < (9 / 8 : ℝ) by norm_num)
    norm_num at h
    exact h
  have hLog : Real.log (3 / 2 : ℝ) =
      Real.log (7 / 6 : ℝ) +
      Real.log (8 / 7 : ℝ) + Real.log (9 / 8 : ℝ) := by
    calc
      Real.log (3 / 2 : ℝ) =
          Real.log (((7 / 6 : ℝ) * (8 / 7 : ℝ)) * (9 / 8 : ℝ)) := by
        congr 1
        norm_num
      _ = Real.log (7 / 6 : ℝ) +
          Real.log (8 / 7 : ℝ) + Real.log (9 / 8 : ℝ) := by
        rw [Real.log_mul
          (by norm_num : ((7 / 6 : ℝ) * (8 / 7 : ℝ)) ≠ 0)
          (by norm_num : (9 / 8 : ℝ) ≠ 0),
          Real.log_mul
          (by norm_num : (7 / 6 : ℝ) ≠ 0)
          (by norm_num : (8 / 7 : ℝ) ≠ 0)]
  have hSum : (3 / 8 : ℝ) ≤ (1 / 7 : ℝ) + 1 / 8 + 1 / 9 := by norm_num
  linarith only [h7, h8, h9, hLog, hSum]

/-- The exact original beta0=log(3/2)/64 is at least 3/512. -/
theorem p4Q2PZ37AKP_originalFixedCoupling_ge_threeOver512 :
    (3 / 512 : ℝ) ≤ GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling := by
  have h := p4Q2PZ37AKP_threeEighths_le_log_threeHalves
  change (3 / 512 : ℝ) ≤ Real.log (3 / 2 : ℝ) / 64
  linarith only [h]

/-- The pinned Mathlib logarithm estimate gives the required strict
upper rational bound for log 4. -/
theorem p4Q2PZ37AKP_log_four_lt_139Over100 :
    Real.log 4 < (139 / 100 : ℝ) := by
  have h : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith only [h, heq]

local notation "GP" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKP_group : IsTopologicalGroup GP :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKP_compact : CompactSpace GP :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKP_countable : SecondCountableTopology GP :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKP_measurable : MeasurableSpace GP :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKP_borel : BorelSpace GP :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKP_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "pP" => p4Q2PZ37AFZ_plaquetteCount H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- Exact original plaquette-count lower bound above the H=13 cutoff. -/
theorem p4Q2PZ37AKP_originalPlaquetteCount_ge_fourteen
    (hH : 14 ≤ H) : 81000 ≤ pP := by
  have hHR : (14 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hCube : (15 : ℝ) ^ 3 ≤ ((H : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

/-- Original beta0 violates AKN's SCALAR sufficient no-witness test for
each H>=14; this is NOT a positive AJA witness existence theorem. -/
theorem p4Q2PZ37AKP_originalFixedCoupling_quadratic_gt_log_four_of_ge_fourteen
    (hH : 14 ≤ H) :
    Real.log 4 < beta0 ^ 2 * pP / 2 := by
  have hb : (3 / 512 : ℝ) ≤ beta0 :=
    p4Q2PZ37AKP_originalFixedCoupling_ge_threeOver512
  have hp : (81000 : ℝ) ≤ pP :=
    p4Q2PZ37AKP_originalPlaquetteCount_ge_fourteen H hH
  have hbSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 512 : ℝ)) hb 2
  have hMul1 :=
    mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 :=
    mul_le_mul_of_nonneg_left hp (sq_nonneg (3 / 512 : ℝ))
  have hHigh : (139 / 100 : ℝ) < beta0 ^ 2 * pP / 2 := by
    nlinarith only [hMul1, hMul2]
  exact lt_trans p4Q2PZ37AKP_log_four_lt_139Over100 hHigh

/-- Sharp finite-H characterization of the original fixed-beta0
quadratic criterion used in AKN (not of actual witness existence). -/
theorem p4Q2PZ37AKP_originalFixedCoupling_quadratic_iff_le_thirteen :
    beta0 ^ 2 * pP / 2 ≤ Real.log 4 ↔ H ≤ 13 := by
  constructor
  · intro h
    by_contra hn
    have h14 : 14 ≤ H := by omega
    exact (not_le_of_gt
      (p4Q2PZ37AKP_originalFixedCoupling_quadratic_gt_log_four_of_ge_fourteen
        H h14)) h
  · exact p4Q2PZ37AKO_originalFixedCoupling_quadratic_at_le_thirteen H

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKP_threeEighths_le_log_threeHalves
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKP_originalFixedCoupling_ge_threeOver512
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKP_log_four_lt_139Over100
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKP_originalPlaquetteCount_ge_fourteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKP_originalFixedCoupling_quadratic_gt_log_four_of_ge_fourteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKP_originalFixedCoupling_quadratic_iff_le_thirteen
