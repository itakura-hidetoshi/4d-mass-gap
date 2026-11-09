import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalVarianceRootCriticalComparisonV5_PZ37AIR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeWardCenterMixedHaarExactV5_PZ37AHU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIS — genuine gauge-Ward crossing improvement beyond the old threshold

Retain the ORIGINAL complete SU(2) Wilson action, both spatial halfweights,
signed ZW physical L2 source and continuous representative, normalized original
spatial product Haar, and AIG's unchanged epsilon and strict negative region.
All previous assumptions, results, roots, pins and resource budgets remain.

AHU's exact ORIGINAL mixed Haar moment integral(f_H^2*Cross_H)=p_H*V_H
cancels the integrated exponential tangent. Thus the actual crossing-weighted
second moment is >= exp(-beta*p_H)*V_H for EVERY real beta. For beta>0 this
improves AIN's previous exp(-2*beta*p_H) floor without replacing any physical object.

Retaining AIN's signed quadratic correction and BOTH halfweights gives
  T_beta f0(B) <= -D_H(beta)  whenever f_H(B)<=0, beta>0,
  D_H(beta)=beta*exp(-5*beta*p_H/2)*V_H.
The original AIG margin satisfies the exact identity
  2*epsilon_H(beta)=(Zcross_H(beta)*exp(beta*p_H/2))*D_H(beta).
AIQ's genuine character bound makes this factor <=1 for 0<=beta<=1.
Consequently the SAME strict full-margin negative region has genuine Haar
mass >=1/2 for EVERY finite H and 0<beta<=1, INCLUDING beta=1.

This interval and mass bound are independent of H. The certified negative
amplitudes and the configurations are not. Their exact p_H=24*(H+1)^3
dependence and the bound V_H<=p_H^2/4 remain explicit below.

At beta=1 the old AIR comparison factor is already >2. At the unchanged
fixed beta0, EVERY finite volume is covered, while for H>=2 the old floor
is strictly below the same original epsilon. These are explicit successes
beyond the OLD sufficient comparison, not physical critical-point claims.

No arbitrary-positive-coupling full-margin half-Haar claim, volume-uniform
positive amplitude or coercivity, operator negative eigenvalue, Hamiltonian
spectral gap, or continuum four-dimensional Yang-Mills mass gap is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIS_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIS_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIS_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIS_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIS_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2

local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "r" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "lambdaH" => p4Q2PZ37AIP_closedHalfHaarCouplingCutoff H
local notation "thetaH" => p4Q2PZ37AIR_criticalComparisonCoupling H
local notation "F" => p4Q2PZ37AIR_originalMarginComparisonFactor H
local notation "delta" => p4Q2PZ37AIO_sourceNonpositiveVarianceFloor H

local instance p4Q2PZ37AIS_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- AHU's already proved gauge-Ward evaluation cancels the actual
centered-crossing moment with the genuine source-square weight. -/
theorem p4Q2PZ37AIS_originalSourceSquare_centeredCrossingHaar_zero
    (B : Cfg) :
    (∫ A : Cfg, (fCont A) ^ 2 * (Cross A B - pH) ∂muH) = 0 := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hc : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMixed : Integrable (fun A : Cfg => (fCont A) ^ 2 * Cross A B) muH :=
    ((hf.pow 2).mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hExact : (∫ A : Cfg, (fCont A) ^ 2 * Cross A B ∂muH) = pH * Vsrc :=
    p4Q2PZ37AHU_originalMixedCrossing_exact H B
  calc
    (∫ A : Cfg, (fCont A) ^ 2 * (Cross A B - pH) ∂muH) =
        ∫ A : Cfg, (fCont A) ^ 2 * Cross A B - pH * (fCont A) ^ 2 ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = (∫ A : Cfg, (fCont A) ^ 2 * Cross A B ∂muH) -
        pH * (∫ A : Cfg, (fCont A) ^ 2 ∂muH) := by
      rw [integral_sub hMixed (hSq.const_mul pH), integral_const_mul]
    _ = pH * Vsrc - pH * Vsrc := by rw [hExact]; rfl
    _ = 0 := sub_self _

/-- Exponential tangent at the exact gauge-Ward mean p_H.  This improves
AIN's exp(-2*beta*p_H) variance floor to exp(-beta*p_H).  The tangent
inequality is valid for every real beta; positivity is needed only when
this lower bound is later used in a signed-transfer correction. -/
theorem p4Q2PZ37AIS_originalCrossingSecondMoment_wardLower
    (beta : ℝ) (B : Cfg) :
    Real.exp (-(beta * pH)) * Vsrc ≤
      ∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hc : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCentered : Integrable
      (fun A : Cfg => (fCont A) ^ 2 * (Cross A B - pH)) muH :=
    ((hf.pow 2).mul (hc.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLower : Integrable
      (fun A : Cfg => Real.exp (-(beta * pH)) *
        ((fCont A) ^ 2 + (-beta) * ((fCont A) ^ 2 * (Cross A B - pH)))) muH :=
    (hSq.add (hCentered.const_mul (-beta))).const_mul _
  have hKSq : Integrable (fun A : Cfg => KC beta A B * (fCont A) ^ 2) muH :=
    ((p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B).mul
      (hf.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      Real.exp (-(beta * pH)) *
          ((fCont A) ^ 2 + (-beta) * ((fCont A) ^ 2 * (Cross A B - pH))) ≤
        KC beta A B * (fCont A) ^ 2 := by
    have hExp : Real.exp (-(beta * pH)) *
        Real.exp (-(beta * (Cross A B - pH))) = KC beta A B := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann,
        ← Real.exp_add]
      congr 1
      ring
    have hTangent := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (-(beta * (Cross A B - pH))))
      (Real.exp_pos (-(beta * pH))).le
    rw [hExp] at hTangent
    calc
      _ = (Real.exp (-(beta * pH)) *
          (-(beta * (Cross A B - pH)) + 1)) * (fCont A) ^ 2 := by ring
      _ ≤ KC beta A B * (fCont A) ^ 2 :=
        mul_le_mul_of_nonneg_right hTangent (sq_nonneg (fCont A))
  have hLowerIntegral :
      (∫ A : Cfg, Real.exp (-(beta * pH)) *
        ((fCont A) ^ 2 + (-beta) * ((fCont A) ^ 2 * (Cross A B - pH))) ∂muH) =
      Real.exp (-(beta * pH)) * Vsrc := by
    rw [integral_const_mul, integral_add hSq (hCentered.const_mul (-beta)),
      integral_const_mul, p4Q2PZ37AIS_originalSourceSquare_centeredCrossingHaar_zero H B]
    change Real.exp (-(beta * pH)) * (Vsrc + (-beta) * 0) =
      Real.exp (-(beta * pH)) * Vsrc
    ring
  calc
    Real.exp (-(beta * pH)) * Vsrc =
        ∫ A : Cfg, Real.exp (-(beta * pH)) *
          ((fCont A) ^ 2 + (-beta) * ((fCont A) ^ 2 * (Cross A B - pH))) ∂muH :=
      hLowerIntegral.symm
    _ ≤ ∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH :=
      integral_mono hLower hKSq hPoint

/-- A new auxiliary floor for the SAME physical transfer and signed source.
The original AIG margin is not redefined. -/
def p4Q2PZ37AIS_sourceNonpositiveWardFloor (beta : ℝ) : ℝ :=
  beta * Real.exp (-(5 * beta * pH / 2)) * Vsrc

local notation "wardFloor" => p4Q2PZ37AIS_sourceNonpositiveWardFloor H

theorem p4Q2PZ37AIS_sourceNonpositiveWardFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < wardFloor beta := by
  exact mul_pos (mul_pos hbeta (Real.exp_pos _))
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2

/-- Exact improvement factor over the old AIO auxiliary floor. -/
theorem p4Q2PZ37AIS_wardFloor_eq_exp_mul_previous (beta : ℝ) :
    wardFloor beta = Real.exp (beta * pH) *
      p4Q2PZ37AIO_sourceNonpositiveVarianceFloor H beta := by
  have hExp : Real.exp (beta * pH) * Real.exp (-(7 * beta * pH / 2)) =
      Real.exp (-(5 * beta * pH / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold p4Q2PZ37AIS_sourceNonpositiveWardFloor
    p4Q2PZ37AIO_sourceNonpositiveVarianceFloor
  rw [← hExp]
  ring

theorem p4Q2PZ37AIS_previousFloor_lt_wardFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AIO_sourceNonpositiveVarianceFloor H beta < wardFloor beta := by
  have hExp : (1 : ℝ) < Real.exp (beta * pH) :=
    Real.one_lt_exp_iff.mpr (mul_pos hbeta (p4Q2PZ37AHN_count_pos H))
  rw [p4Q2PZ37AIS_wardFloor_eq_exp_mul_previous H beta]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hExp
    (p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos H beta hbeta)

/-- Retain AIN's signed quadratic estimate and substitute the stronger
genuine gauge-Ward crossing second moment, for every positive coupling. -/
theorem p4Q2PZ37AIS_originalRightWeightedTransfer_le_negativeWardVariance
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    Real.exp ((beta / 2) * W B) * T beta f0 B ≤
      -(beta * Real.exp (-(2 * beta * pH)) * Vsrc) := by
  have hSource : Zcross beta * r beta ^ 4 * fCont B ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (p4Q2PZ37AIF_originalCrossingPartition_pos H beta)
        (pow_pos (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos beta hbeta) 4)).le hB
  have hSourceScaled := mul_nonpos_of_nonneg_of_nonpos
    (Real.exp_pos (-(beta * (pH / 2)))).le hSource
  have hCoefficient : 0 ≤ Real.exp (-(beta * (pH / 2))) *
      (beta * Real.exp (-(beta * (pH / 2)))) := by positivity
  have hSecond := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIS_originalCrossingSecondMoment_wardLower H beta B) hCoefficient
  have hExp : Real.exp (-(beta * (pH / 2))) *
      (Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * pH))) =
        Real.exp (-(2 * beta * pH)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hFloor : Real.exp (-(beta * (pH / 2))) *
      (beta * Real.exp (-(beta * (pH / 2)))) *
        (Real.exp (-(beta * pH)) * Vsrc) =
      beta * Real.exp (-(2 * beta * pH)) * Vsrc := by
    calc
      _ = beta * (Real.exp (-(beta * (pH / 2))) *
          (Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * pH)))) * Vsrc := by ring
      _ = _ := by rw [hExp]
  calc
    _ ≤ Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          (beta * Real.exp (-(beta * (pH / 2)))) *
            (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) :=
      p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper H beta hbeta.le B
    _ ≤ -(Real.exp (-(beta * (pH / 2))) *
        (beta * Real.exp (-(beta * (pH / 2)))) *
          (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
      nlinarith only [hSourceScaled]
    _ ≤ -(Real.exp (-(beta * (pH / 2))) *
        (beta * Real.exp (-(beta * (pH / 2)))) *
          (Real.exp (-(beta * pH)) * Vsrc)) := neg_le_neg hSecond
    _ = _ := by rw [hFloor]

/-- Restore the original right halfweight on W(B)<=p_H. The 5/2
exponent contains both spatial halfweights, the unchanged scalar
correction, and the actual improved crossing estimate. -/
theorem p4Q2PZ37AIS_originalTransfer_le_negativeWardFloor
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    T beta f0 B ≤ -(wardFloor beta) := by
  have hW := p4Q2PZ37AIO_originalAction_le_count_of_source_nonpos H B hB
  have hInverse : Real.exp (-(beta * pH / 2)) ≤ Real.exp (-(beta / 2) * W B) := by
    apply Real.exp_le_exp.mpr
    have hMul := mul_le_mul_of_nonneg_left hW hbeta.le
    nlinarith only [hMul]
  have hNonpos : -(beta * Real.exp (-(2 * beta * pH)) * Vsrc) ≤ 0 :=
    neg_nonpos.mpr (mul_pos (mul_pos hbeta (Real.exp_pos _))
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2).le
  have hCancel : Real.exp (-(beta / 2) * W B) *
      Real.exp ((beta / 2) * W B) = 1 := by
    have hArg : -(beta / 2) * W B + (beta / 2) * W B = 0 := by ring
    rw [← Real.exp_add, hArg, Real.exp_zero]
  have hExp : Real.exp (-(beta * pH / 2)) * Real.exp (-(2 * beta * pH)) =
      Real.exp (-(5 * beta * pH / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    T beta f0 B = Real.exp (-(beta / 2) * W B) *
        (Real.exp ((beta / 2) * W B) * T beta f0 B) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ Real.exp (-(beta / 2) * W B) *
        (-(beta * Real.exp (-(2 * beta * pH)) * Vsrc)) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIS_originalRightWeightedTransfer_le_negativeWardVariance H beta hbeta B hB)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-(beta * pH / 2)) *
        (-(beta * Real.exp (-(2 * beta * pH)) * Vsrc)) :=
      mul_le_mul_of_nonpos_right hInverse hNonpos
    _ = -(beta * (Real.exp (-(beta * pH / 2)) *
        Real.exp (-(2 * beta * pH))) * Vsrc) := by ring
    _ = -(wardFloor beta) := by rw [hExp]; rfl

/-- Exact identity for the UNCHANGED AIG negative margin. Only the
auxiliary transfer floor has improved; the original partition is retained. -/
theorem p4Q2PZ37AIS_originalNegativeMargin_wardRatio_identity (beta : ℝ) :
    2 * margin beta =
      (Zcross beta * Real.exp (beta * pH / 2)) * wardFloor beta := by
  have hExp : Real.exp (beta * pH / 2) * Real.exp (-(5 * beta * pH / 2)) =
      Real.exp (-(2 * beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
    p4Q2PZ37AIS_sourceNonpositiveWardFloor
  rw [← hExp]
  ring

/-- AIQ's original character bound, with the new Ward comparison exponent.
This scalar Gaussian estimate is valid for every real beta. -/
theorem p4Q2PZ37AIS_originalWardMarginFactor_le_gaussian (beta : ℝ) :
    Zcross beta * Real.exp (beta * pH / 2) ≤
      Real.exp (pH * (beta ^ 2 - beta) / 2) := by
  calc
    _ ≤ Real.exp (pH * (-beta + beta ^ 2 / 2)) * Real.exp (beta * pH / 2) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian H beta) (Real.exp_pos _).le
    _ = Real.exp (pH * (beta ^ 2 - beta) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The coupling interval is independent of H. No claim that the
negative amplitudes or configurations are independent of H is made. -/
theorem p4Q2PZ37AIS_originalWardMarginFactor_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    Zcross beta * Real.exp (beta * pH / 2) ≤ 1 := by
  have hQuadratic : beta ^ 2 - beta ≤ 0 := by
    nlinarith only [mul_nonneg hbeta (sub_nonneg.mpr hOne)]
  have hExponent : pH * (beta ^ 2 - beta) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (p4Q2PZ37AHN_count_pos H).le hQuadratic)
      (by norm_num)
  exact (p4Q2PZ37AIS_originalWardMarginFactor_le_gaussian H beta).trans
    (Real.exp_le_one_iff.mpr hExponent)

/-- A factor-two comparison, including beta=1, for the old full margin. -/
theorem p4Q2PZ37AIS_twice_originalNegativeMargin_le_wardFloor
    (beta : ℝ) (hbeta : 0 < beta) (hOne : beta ≤ 1) :
    2 * margin beta ≤ wardFloor beta := by
  rw [p4Q2PZ37AIS_originalNegativeMargin_wardRatio_identity H beta]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (p4Q2PZ37AIS_originalWardMarginFactor_le_one H beta hbeta.le hOne)
    (p4Q2PZ37AIS_sourceNonpositiveWardFloor_pos H beta hbeta).le

theorem p4Q2PZ37AIS_originalNegativeMargin_lt_wardFloor
    (beta : ℝ) (hbeta : 0 < beta) (hOne : beta ≤ 1) :
    margin beta < wardFloor beta := by
  have hComparison := p4Q2PZ37AIS_twice_originalNegativeMargin_le_wardFloor H beta hbeta hOne
  have hPositive := p4Q2PZ37AIS_sourceNonpositiveWardFloor_pos H beta hbeta
  linarith only [hComparison, hPositive]

/-- Includes the source zero set without assuming it is Haar null. -/
theorem p4Q2PZ37AIS_originalSource_nonpos_subset_fullNegativeRegion
    (beta : ℝ) (hbeta : 0 < beta) (hOne : beta ≤ 1) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta := by
  intro B hB
  exact (p4Q2PZ37AIS_originalTransfer_le_negativeWardFloor H beta hbeta B hB).trans_lt
    (neg_lt_neg (p4Q2PZ37AIS_originalNegativeMargin_lt_wardFloor H beta hbeta hOne))

/-- The SAME original strict full-margin region has genuine Haar mass
at least one half for every finite H and every 0<beta<=1. -/
theorem p4Q2PZ37AIS_originalFullNegativeRegion_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) (hOne : beta ≤ 1) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  (p4Q2PZ37AIN_originalSource_nonpos_Haar_half H).trans
    (measure_mono
      (p4Q2PZ37AIS_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta hOne))

theorem p4Q2PZ37AIS_originalFullNegativeRegion_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) (hOne : beta ≤ 1) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) := by
  have h := ENNReal.toReal_mono (measure_ne_top muH (Region beta))
    (p4Q2PZ37AIS_originalFullNegativeRegion_Haar_half H beta hbeta hOne)
  simpa [Measure.real] using h

/-- The old implicit comparison threshold lies strictly below the new
included endpoint. This is not a physical critical-coupling assertion. -/
theorem p4Q2PZ37AIS_previousComparisonThreshold_lt_one :
    p4Q2PZ37AIR_criticalComparisonCoupling H < 1 := by
  have hThreshold := (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.1
  have hCutoff := p4Q2PZ37AIP_closedCutoff_le_oneDiv24 H
  linarith only [hThreshold, hCutoff]

/-- At beta=1 the previous sufficient factor is strictly ABOVE two,
while the unchanged physical full-margin region still has half Haar mass. -/
theorem p4Q2PZ37AIS_oldComparisonObstruction_newEndpoint_certificate :
    p4Q2PZ37AIR_criticalComparisonCoupling H < 1 ∧
      2 < p4Q2PZ37AIR_originalMarginComparisonFactor H 1 ∧
      (1 / 2 : ℝ) ≤ Measure.real muH (Region 1) := by
  have hThreshold := p4Q2PZ37AIS_previousComparisonThreshold_lt_one H
  refine ⟨hThreshold, ?_, ?_⟩
  · exact (p4Q2PZ37AIR_originalMarginFactor_gt_two_iff H 1 (by norm_num)).mpr hThreshold
  · exact p4Q2PZ37AIS_originalFullNegativeRegion_realHaar_half H 1 (by norm_num) le_rfl

/-- The unchanged positive fixed beta0 is now covered at EVERY finite H. -/
theorem p4Q2PZ37AIS_fixedCoupling_fullNegativeRegion_realHaar_half :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta0) := by
  have hBound := p4Q2PZ37AIB_fixedCoupling_rationalInterval.2
  exact p4Q2PZ37AIS_originalFullNegativeRegion_realHaar_half H beta0
    p4Q2PZ37ADC_fixedCoupling_pos (by linarith only [hBound])

/-- Explicit volume dependence retained in the actual source variance. -/
theorem p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare :
    Vsrc ≤ pH ^ 2 / 4 := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) : (fCont A) ^ 2 ≤ (pH / 2) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (fCont A))
      (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A) 2
    simpa only [sq_abs] using h
  calc
    Vsrc = ∫ A : Cfg, (fCont A) ^ 2 ∂muH := rfl
    _ ≤ ∫ _A : Cfg, (pH / 2) ^ 2 ∂muH :=
      integral_mono hSq (integrable_const (μ := muH) _) hPoint
    _ = pH ^ 2 / 4 := by
      simp only [integral_const, probReal_univ, one_smul]
      ring

/-- A coupling interval independent of H does not remove the explicit
finite-volume exponential in the certified negative amplitude. -/
theorem p4Q2PZ37AIS_wardFloor_le_explicitVolumeBound
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    wardFloor beta ≤ beta * Real.exp (-(5 * beta * pH / 2)) * (pH ^ 2 / 4) := by
  exact mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H)
    (mul_nonneg hbeta (Real.exp_pos _).le)

/-- Write the true original finite-volume count out explicitly. -/
theorem p4Q2PZ37AIS_wardFloor_exactVolume (beta : ℝ) :
    wardFloor beta = beta * Real.exp (-(60 * beta * ((H : ℝ) + 1) ^ 3)) * Vsrc := by
  unfold p4Q2PZ37AIS_sourceNonpositiveWardFloor
  rw [p4Q2PZ37AIB_plaquetteCount_exact H]
  congr 2
  congr 1
  ring


/-- The unchanged fixed coupling belongs to the new unit coupling interval,
independently of finite volume. -/
theorem p4Q2PZ37AIS_originalFixedCoupling_mem_unitInterval :
    0 < beta0 ∧ beta0 ≤ 1 := by
  refine ⟨p4Q2PZ37ADC_fixedCoupling_pos, ?_⟩
  exact (p4Q2PZ37AIB_fixedCoupling_rationalInterval).2.trans (by norm_num)

/-- A rational bound from the existing genuine plaquette-count identity,
with neither a rescaled coupling nor a floating-point estimate. -/
theorem p4Q2PZ37AIS_originalFixedCoupling_count_ge_twentySevenEighths
    (hH : 2 ≤ H) :
    (27 / 8 : ℝ) ≤ beta0 * pH := by
  have hReal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hBase : (3 : ℝ) ≤ (H : ℝ) + 1 := by linarith only [hReal]
  have hCube : (3 : ℝ) ^ 3 ≤ ((H : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hBase 3
  have hFloor := p4Q2PZ37AIB_originalFixedCoupling_count_cubicFloor H
  nlinarith only [hCube, hFloor]

/-- At H >= 2 the SAME fixed coupling lies strictly past AIQ's OLD
sufficient-comparison ceiling. This is not a transfer-sign obstruction. -/
theorem p4Q2PZ37AIS_oldComparisonCeiling_lt_originalFixedCoupling
    (hH : 2 ≤ H) :
    2 * lambdaH < beta0 := by
  have hLog : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  have hLower :=
    p4Q2PZ37AIS_originalFixedCoupling_count_ge_twentySevenEighths H hH
  apply (mul_lt_mul_right (p4Q2PZ37AHN_count_pos H)).mp
  nlinarith only [hLog, hCount, hLower]

/-- AIR's exact OLD comparison threshold is also strictly below beta0. -/
theorem p4Q2PZ37AIS_oldCriticalComparison_lt_originalFixedCoupling
    (hH : 2 ≤ H) :
    thetaH < beta0 :=
  (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.1.trans
    (p4Q2PZ37AIS_oldComparisonCeiling_lt_originalFixedCoupling H hH)

/-- Strict failure of the OLD partition comparison at the unchanged
fixed coupling. No claim of physical failure is made. -/
theorem p4Q2PZ37AIS_oldMarginComparison_at_originalFixedCoupling_gt_two
    (hH : 2 ≤ H) :
    2 < F beta0 :=
  (p4Q2PZ37AIR_originalMarginFactor_gt_two_iff H beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le).mpr
      (p4Q2PZ37AIS_oldCriticalComparison_lt_originalFixedCoupling H hH)

/-- The OLD AIO floor is genuinely below the SAME AIG epsilon in these
volumes; a later success must therefore use an additional transfer estimate. -/
theorem p4Q2PZ37AIS_oldVarianceFloor_lt_originalFixedMargin
    (hH : 2 ≤ H) :
    delta beta0 < margin beta0 :=
  (p4Q2PZ37AIR_originalFloor_lt_negativeMargin_iff H beta0
    p4Q2PZ37ADC_fixedCoupling_pos).mpr
      (p4Q2PZ37AIS_oldCriticalComparison_lt_originalFixedCoupling H hH)


/-- The SAME fixed physical problem: the previous auxiliary floor fails,
while the additional genuine transfer estimate proves half Haar mass. -/
theorem p4Q2PZ37AIS_fixedCoupling_oldObstruction_newHalfHaar_certificate
    (hH : 2 ≤ H) :
    thetaH < beta0 ∧ 2 < F beta0 ∧
      delta beta0 < margin beta0 ∧ margin beta0 < wardFloor beta0 ∧
      (1 / 2 : ℝ) ≤ Measure.real muH (Region beta0) := by
  refine ⟨p4Q2PZ37AIS_oldCriticalComparison_lt_originalFixedCoupling H hH,
    p4Q2PZ37AIS_oldMarginComparison_at_originalFixedCoupling_gt_two H hH,
    p4Q2PZ37AIS_oldVarianceFloor_lt_originalFixedMargin H hH, ?_,
    p4Q2PZ37AIS_fixedCoupling_fullNegativeRegion_realHaar_half H⟩
  exact p4Q2PZ37AIS_originalNegativeMargin_lt_wardFloor H beta0
    p4Q2PZ37ADC_fixedCoupling_pos
    p4Q2PZ37AIS_originalFixedCoupling_mem_unitInterval.2

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalSourceSquare_centeredCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalCrossingSecondMoment_wardLower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_sourceNonpositiveWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_sourceNonpositiveWardFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_wardFloor_eq_exp_mul_previous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_previousFloor_lt_wardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalRightWeightedTransfer_le_negativeWardVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalTransfer_le_negativeWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalNegativeMargin_wardRatio_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalWardMarginFactor_le_gaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalWardMarginFactor_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_twice_originalNegativeMargin_le_wardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalNegativeMargin_lt_wardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalSource_nonpos_subset_fullNegativeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalFullNegativeRegion_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalFullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_previousComparisonThreshold_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_oldComparisonObstruction_newEndpoint_certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_fixedCoupling_fullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_wardFloor_le_explicitVolumeBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_wardFloor_exactVolume
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalFixedCoupling_mem_unitInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_originalFixedCoupling_count_ge_twentySevenEighths
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_oldComparisonCeiling_lt_originalFixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_oldCriticalComparison_lt_originalFixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_oldMarginComparison_at_originalFixedCoupling_gt_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_oldVarianceFloor_lt_originalFixedMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIS_fixedCoupling_oldObstruction_newHalfHaar_certificate
