import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH22ComplementBorelDescentV5_PZ37AKY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuadraticFrontierV5_PZ37AKP
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKZ — Stepwise original H22, H23, H24, H25 AKX feasibility frontier

No original Wilson SU(2) operator, physical source, normalized transfer,
Haar measure, negative margin, top projection, AJA budget or fixed
beta0=log(3/2)/64 is modified. Exactly the AKW/AKX sufficient test is
examined at successive original volumes, with p_H=24*(H+1)^3.

The known genuine original AIT/AIW lower bound is r_H>=1/2.
For H<=24 the scalar AKX upper threshold 4*exp(-q_H) is strictly
ABOVE 1/2, which means it is not excluded by the lower bound;
this alone supplies NO true Haar upper mass bound or AJA no-witness.
For every H>=25, the AKX threshold is strictly BELOW 1/2, so
the SAME AKX sufficient test is actually impossible in the true
original model. This does NOT imply an AJA witness exists.

The critical rational coupling floor beta0>=201/32000 is proved
using pinned Mathlib Real.exp_bound n=3 (not floating computation),
while Real.log_two_gt_d9/lt_d9 bounds log 8. Thus the frontier
is established without introducing an assumed Haar mass table.

Append-only, tighten-only, same root, standard-three axiom audit.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- Rigorous original logarithm floor, using pinned Real.exp_bound
with the actual third-Taylor remainder, rather than a decimal guess. -/
theorem p4Q2PZ37AKZ_log_threeHalves_ge_201Over500 :
    (201 / 500 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
  have hx : |(201 / 500 : ℝ)| ≤ (1 : ℝ) := by norm_num
  have hPoly :
      (∑ m ∈ Finset.range 3,
        (201 / 500 : ℝ) ^ m / (m.factorial : ℝ)) =
      1 + (201 / 500 : ℝ) + (201 / 500 : ℝ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hBound := Real.exp_bound (x := (201 / 500 : ℝ)) hx (n := 3) (by decide)
  rw [hPoly] at hBound
  have hRem :
      |Real.exp (201 / 500 : ℝ) -
        (1 + (201 / 500 : ℝ) + (201 / 500 : ℝ) ^ 2 / 2)| ≤
        |(201 / 500 : ℝ)| ^ 3 * (2 / 9 : ℝ) := by
    convert hBound using 1
    norm_num [Nat.factorial]
  have hUpper := (abs_le.mp hRem).2
  have hRational :
      (1 + (201 / 500 : ℝ) + (201 / 500 : ℝ) ^ 2 / 2) +
        |(201 / 500 : ℝ)| ^ 3 * (2 / 9 : ℝ) ≤ (3 / 2 : ℝ) := by
    norm_num
  have hExp : Real.exp (201 / 500 : ℝ) ≤ (3 / 2 : ℝ) := by
    linarith only [hUpper, hRational]
  have hLog : Real.exp (201 / 500 : ℝ) ≤
      Real.exp (Real.log (3 / 2 : ℝ)) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < (3 / 2 : ℝ))]
    exact hExp
  exact Real.exp_le_exp.mp hLog

theorem p4Q2PZ37AKZ_originalFixedCoupling_ge_201Over32000 :
    (201 / 32000 : ℝ) ≤ GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling := by
  have h := p4Q2PZ37AKZ_log_threeHalves_ge_201Over500
  change (201 / 32000 : ℝ) ≤ Real.log (3 / 2 : ℝ) / 64
  linarith only [h]

theorem p4Q2PZ37AKZ_log_eight_gt_two :
    (2 : ℝ) < Real.log 8 := by
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith only [h, heq]

theorem p4Q2PZ37AKZ_log_eight_lt_52Over25 :
    Real.log 8 < (52 / 25 : ℝ) := by
  have h : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith only [h, heq]

local notation "GZ" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKZ_group : IsTopologicalGroup GZ :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKZ_compact : CompactSpace GZ :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKZ_countable : SecondCountableTopology GZ :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKZ_measurable : MeasurableSpace GZ :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKZ_borel : BorelSpace GZ :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKZ_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgZ" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muZ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "pZ" => p4Q2PZ37AFZ_plaquetteCount H
local notation "qZ" => 44 * beta0 ^ 2 * pZ / 351
local notation "uZ" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mZ" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "negativeZ" =>
  (fun A : CfgZ =>
    uZ beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
      -(mZ beta0 p4Q2PZ37ADC_fixedCoupling_pos.le))
local notation "rZ" => Measure.real muZ negativeZ

local instance p4Q2PZ37AKZ_probability : IsProbabilityMeasure muZ := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

theorem p4Q2PZ37AKZ_originalPlaquetteCount_le_24
    (hH : H ≤ 24) : pZ ≤ 375000 := by
  have hHR : (H : ℝ) ≤ 24 := by exact_mod_cast hH
  have hCube : ((H : ℝ) + 1) ^ 3 ≤ (25 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

theorem p4Q2PZ37AKZ_originalPlaquetteCount_ge_25
    (hH : 25 ≤ H) : (421824 : ℝ) ≤ pZ := by
  have hHR : (25 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hCube : (26 : ℝ) ^ 3 ≤ ((H : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 26)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

/-- H<=24: the exact original scalar AKX threshold is still
compatible with the proved Haar lower half. No upper mass follows. -/
theorem p4Q2PZ37AKZ_originalSmallCoupling_q_lt_logEight_of_le24
    (hH : H ≤ 24) : qZ < Real.log 8 := by
  have hb0 : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hp : pZ ≤ (375000 : ℝ) :=
    p4Q2PZ37AKZ_originalPlaquetteCount_le_24 H hH
  have hbSq := pow_le_pow_left₀ hb0 hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 / 156 : ℝ))
  have hSmall : qZ < (2 : ℝ) := by
    nlinarith only [hMul1, hMul2]
  exact lt_trans hSmall p4Q2PZ37AKZ_log_eight_gt_two

/-- The H22, H23 and H24 thresholds are all strictly above the
already-proved r_H>=1/2 lower mass, so they can be tested independently.
This is NOT an upper mass estimate. -/
theorem p4Q2PZ37AKZ_originalSmallCoupling_HaarThreshold_gt_half_of_le24
    (hH : H ≤ 24) :
    (1 / 2 : ℝ) < 4 * Real.exp (-qZ) := by
  have hQ : qZ < Real.log 8 :=
    p4Q2PZ37AKZ_originalSmallCoupling_q_lt_logEight_of_le24 H hH
  have hExp : Real.exp qZ < (8 : ℝ) := by
    have h := Real.exp_lt_exp.mpr hQ
    rw [Real.exp_log (by norm_num : (0 : ℝ) < (8 : ℝ))] at h
    exact h
  have hCancel : Real.exp qZ * Real.exp (-qZ) = 1 := by
    rw [← Real.exp_add]
    simp
  have hScale := mul_lt_mul_of_pos_right hExp (Real.exp_pos (-qZ))
  rw [hCancel] at hScale
  linarith only [hScale]

/-- AIT/AIW give the original genuine strict-negative Haar lower mass
for ALL H, independently of all proposed AKX scalar thresholds. -/
theorem p4Q2PZ37AKZ_originalGenuineNegativeHaarMass_ge_half :
    (1 / 2 : ℝ) ≤ rZ := by
  have hSeven : beta0 ≤ (7 : ℝ) := by
    have h := (p4Q2PZ37AIB_fixedCoupling_rationalInterval).2
    linarith only [h]
  have hHalf :=
    p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_of_le_seven
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos hSeven
  rw [← p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le] at hHalf
  exact hHalf

/-- H>=25: strict rational lower beta bound forces the genuine AKX
scalar exponential penalty beyond log 8, with no Haar mass guess. -/
theorem p4Q2PZ37AKZ_originalSmallCoupling_logEight_lt_q_of_ge25
    (hH : 25 ≤ H) : Real.log 8 < qZ := by
  have hb : (201 / 32000 : ℝ) ≤ beta0 :=
    p4Q2PZ37AKZ_originalFixedCoupling_ge_201Over32000
  have hp : (421824 : ℝ) ≤ pZ :=
    p4Q2PZ37AKZ_originalPlaquetteCount_ge_25 H hH
  have hbSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (201 / 32000 : ℝ)) hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (201 / 32000 : ℝ))
  have hLarge : (52 / 25 : ℝ) < qZ := by
    nlinarith only [hMul1, hMul2]
  exact lt_trans p4Q2PZ37AKZ_log_eight_lt_52Over25 hLarge

theorem p4Q2PZ37AKZ_originalAKX_threshold_lt_half_of_ge25
    (hH : 25 ≤ H) : 4 * Real.exp (-qZ) < (1 / 2 : ℝ) := by
  have hQ : Real.log 8 < qZ :=
    p4Q2PZ37AKZ_originalSmallCoupling_logEight_lt_q_of_ge25 H hH
  have hExp : (8 : ℝ) < Real.exp qZ := by
    have h := Real.exp_lt_exp.mpr hQ
    rw [Real.exp_log (by norm_num : (0 : ℝ) < (8 : ℝ))] at h
    exact h
  have hCancel : Real.exp qZ * Real.exp (-qZ) = 1 := by
    rw [← Real.exp_add]
    simp
  have hScale := mul_lt_mul_of_pos_right hExp (Real.exp_pos (-qZ))
  rw [hCancel] at hScale
  linarith only [hScale]

/-- The existing sufficient AKX scalar criterion itself is impossible
at every H>=25, because true r_H>=1/2. This is NOT a theorem that
AJA strict finite-power witnesses exist. -/
theorem p4Q2PZ37AKZ_originalAKX_criterion_false_of_ge25
    (hH : 25 ≤ H) :
    ¬ (rZ ≤ 4 * Real.exp (-qZ)) := by
  have hHalf := p4Q2PZ37AKZ_originalGenuineNegativeHaarMass_ge_half H
  have hThreshold := p4Q2PZ37AKZ_originalAKX_threshold_lt_half_of_ge25 H hH
  exact not_le_of_gt (lt_of_lt_of_le hThreshold hHalf)

/-- Sequential original-volume checkpoints, without replacing the model. -/
theorem p4Q2PZ37AKZ_H22_scalarThreshold_compatible :
    (1 / 2 : ℝ) <
      4 * Real.exp (-(44 * beta0 ^ 2 *
        p4Q2PZ37AFZ_plaquetteCount 22 / 351)) :=
  p4Q2PZ37AKZ_originalSmallCoupling_HaarThreshold_gt_half_of_le24 22 (by omega)

theorem p4Q2PZ37AKZ_H23_scalarThreshold_compatible :
    (1 / 2 : ℝ) <
      4 * Real.exp (-(44 * beta0 ^ 2 *
        p4Q2PZ37AFZ_plaquetteCount 23 / 351)) :=
  p4Q2PZ37AKZ_originalSmallCoupling_HaarThreshold_gt_half_of_le24 23 (by omega)

theorem p4Q2PZ37AKZ_H24_scalarThreshold_compatible :
    (1 / 2 : ℝ) <
      4 * Real.exp (-(44 * beta0 ^ 2 *
        p4Q2PZ37AFZ_plaquetteCount 24 / 351)) :=
  p4Q2PZ37AKZ_originalSmallCoupling_HaarThreshold_gt_half_of_le24 24 (by omega)

theorem p4Q2PZ37AKZ_H25_originalAKX_criterion_false :
    ¬ (Measure.real
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 25 2)
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 25 2 =>
          p4Q2PZ37AIW_originalNormalizedSourceTransfer 25 beta0
            p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 25 beta0
                p4Q2PZ37ADC_fixedCoupling_pos.le))
      ≤ 4 * Real.exp (-(44 * beta0 ^ 2 *
        p4Q2PZ37AFZ_plaquetteCount 25 / 351))) :=
  p4Q2PZ37AKZ_originalAKX_criterion_false_of_ge25 25 (by omega)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKZ_log_threeHalves_ge_201Over500
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKZ_originalFixedCoupling_ge_201Over32000
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKZ_log_eight_gt_two
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKZ_log_eight_lt_52Over25
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalPlaquetteCount_le_24
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalPlaquetteCount_ge_25
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalSmallCoupling_q_lt_logEight_of_le24
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalSmallCoupling_HaarThreshold_gt_half_of_le24
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalGenuineNegativeHaarMass_ge_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalSmallCoupling_logEight_lt_q_of_ge25
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalAKX_threshold_lt_half_of_ge25
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_originalAKX_criterion_false_of_ge25
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_H22_scalarThreshold_compatible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_H23_scalarThreshold_compatible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_H24_scalarThreshold_compatible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKZ_H25_originalAKX_criterion_false
