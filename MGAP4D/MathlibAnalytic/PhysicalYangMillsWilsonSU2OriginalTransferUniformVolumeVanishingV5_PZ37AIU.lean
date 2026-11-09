import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalWardGrowingHalfHaarV5_PZ37AIT
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIU — original transfer image vanishes uniformly over boundaries

Retain the ORIGINAL complete SU(2) Wilson action, both spatial halfweights,
signed ZW physical L2 source and its established continuous representative,
genuine normalized Haar, AIG's original positive margin and strict negative
region, all earlier assumptions/results/roots, and the fixed Lean/mathlib
versions and heartbeat budgets.

For every original finite volume H, beta>=0, and EVERY boundary B, prove
  |T_beta f0(B)| <= exp(-(beta/2)*W(B))*(p_H/2)*Zcross_H(beta)
                <= (p_H/2)*Zcross_H(beta).
The LEFT crossing Haar integral is obtained from the actual kernel symmetry
and AIF's right Haar identity. Both original halfweights are retained until
their nonnegative-action estimates are applied. The actual L2 source is linked
to its original continuous representative by AIF's exact transfer identity.

For z(beta) the genuine one-link Haar partition, set rho(beta)=-log z(beta)
and d(beta)=beta*exp(-2*beta). AIP gives 0<d(beta)<=rho(beta) at every beta>0.
The ORIGINAL crossing partition equals exp(-rho(beta)*p_H), with
p_H=24*(H+1)^3. Hence for each FIXED beta>0, all actual source-image amplitudes
are eventually less than any eta>0, uniformly over B in each original volume.
At the unchanged beta0=log(3/2)/64, an explicit bound is
  |T_beta0 f0(B)| <= 12*(H+1)^3*exp(-(H+1)^3/16).

This actual transfer upper bound is independent of AIT's vanishing lower
certificate. It rules out a positive volume-uniform amplitude or negative
depth for THIS original unnormalized transfer/source family at fixed beta.
The unchanged original AIG positive margin also tends to zero. AIT's eventual
half-Haar region and this all-boundary smallness hold at one common volume
cutoff: finite-volume negative regions need not disappear as amplitudes vanish.

No arbitrary volume-dependent coupling, common configuration-space limit,
operator-norm decay, normalized-transfer obstruction, coercivity statement,
negative eigenvalue, Hamiltonian spectral gap, or continuum four-dimensional
Yang-Mills mass gap is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H

local instance p4Q2PZ37AIU_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

section PZ37AIUPartitionDecay

open Filter
open scoped Topology

local notation "pAIU" => p4Q2PZ37AFZ_plaquetteCount
local notation "zAIU" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "ZAIU" => p4Q2PZ37AIF_originalCrossingPartition
local notation "VAIU" => p4Q2PZ37AHN_originalSource_HaarSecondMoment

/-- The exact rate of the ORIGINAL genuine single-link Haar partition.
This is a scalar definition, independent of the finite-volume index. -/
def p4Q2PZ37AIU_originalPartitionDecayRate (beta : ℝ) : ℝ :=
  -Real.log (zAIU beta)

/-- An explicit elementary rate from AIP's genuine energy deficit.
It neither rescales the coupling nor normalizes the original transfer. -/
def p4Q2PZ37AIU_explicitPartitionDecayRate (beta : ℝ) : ℝ :=
  beta * Real.exp (-2 * beta)

local notation "rhoAIU" => p4Q2PZ37AIU_originalPartitionDecayRate
local notation "dAIU" => p4Q2PZ37AIU_explicitPartitionDecayRate

theorem p4Q2PZ37AIU_explicitPartitionDecayRate_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) : 0 ≤ dAIU beta :=
  mul_nonneg hbeta (Real.exp_pos _).le

theorem p4Q2PZ37AIU_explicitPartitionDecayRate_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < dAIU beta :=
  mul_pos hbeta (Real.exp_pos _)

/-- Exact scalar identity for every real coupling, using the proved strict
positivity of the ORIGINAL Haar partition as the logarithm hypothesis. -/
theorem p4Q2PZ37AIU_originalSingleLinkPartition_eq_exp_rate (beta : ℝ) :
    zAIU beta = Real.exp (-(rhoAIU beta)) := by
  unfold p4Q2PZ37AIU_originalPartitionDecayRate
  simpa only [neg_neg] using
    (Real.exp_log (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta)).symm

/-- AIP's strict deficit implies a strictly positive exact rate at every
positive ORIGINAL coupling. No upper restriction on beta is imposed. -/
theorem p4Q2PZ37AIU_originalPartitionDecayRate_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < rhoAIU beta := by
  exact neg_pos.mpr (Real.log_neg
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta)
    (p4Q2PZ37AIP_originalSingleLinkPartition_lt_one beta hbeta))

/-- Convert AIP's genuine additive deficit into an explicit exponential
bound by the scalar tangent inequality. -/
theorem p4Q2PZ37AIU_originalSingleLinkPartition_le_explicitRate
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    zAIU beta ≤ Real.exp (-(dAIU beta)) := by
  have hDeficit : zAIU beta ≤ 1 - dAIU beta :=
    p4Q2PZ37AIP_originalSingleLinkPartition_le_deficit beta hbeta
  calc
    zAIU beta ≤ 1 - dAIU beta := hDeficit
    _ ≤ Real.exp (-(dAIU beta)) := by
      simpa only [sub_eq_add_neg, add_comm] using
        (Real.add_one_le_exp (-(dAIU beta)))

theorem p4Q2PZ37AIU_explicitPartitionDecayRate_le_original
    (beta : ℝ) (hbeta : 0 ≤ beta) : dAIU beta ≤ rhoAIU beta := by
  have hExp : Real.exp (-(rhoAIU beta)) ≤ Real.exp (-(dAIU beta)) := by
    rw [← p4Q2PZ37AIU_originalSingleLinkPartition_eq_exp_rate beta]
    exact p4Q2PZ37AIU_originalSingleLinkPartition_le_explicitRate beta hbeta
  have hNeg := Real.exp_le_exp.mp hExp
  linarith only [hNeg]

theorem p4Q2PZ37AIU_originalPartitionDecayRate_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) : 0 ≤ rhoAIU beta :=
  (p4Q2PZ37AIU_explicitPartitionDecayRate_nonneg beta hbeta).trans
    (p4Q2PZ37AIU_explicitPartitionDecayRate_le_original beta hbeta)

/-- The ORIGINAL crossing partition has exactly exponential volume
dependence. AIP's actual link-count identity supplies the genuine p_H. -/
theorem p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate
    (H : ℕ) (beta : ℝ) :
    ZAIU H beta = Real.exp (-(rhoAIU beta * pAIU H)) := by
  calc
    ZAIU H beta =
        Real.exp (-(rhoAIU beta)) ^
          Nat.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
      simp only [p4Q2PZ37AIF_originalCrossingPartition,
        Fintype.card_eq_nat_card,
        ← p4Q2PZ37AIU_originalSingleLinkPartition_eq_exp_rate beta]
    _ = Real.exp
        ((Nat.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (-(rhoAIU beta))) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(rhoAIU beta * pAIU H)) := by
      rw [p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
      congr 1
      ring

theorem p4Q2PZ37AIU_originalCrossingPartition_le_explicitRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ZAIU H beta ≤ Real.exp (-(dAIU beta * pAIU H)) := by
  rw [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H beta]
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_right
    (p4Q2PZ37AIU_explicitPartitionDecayRate_le_original beta hbeta)
    (p4Q2PZ37AHN_count_pos H).le)

/-- Scalar envelope for the unchanged unnormalized transfer and physical
source. Its relation to the actual transfer is proved separately. -/
def p4Q2PZ37AIU_originalTransferPartitionEnvelope (H : ℕ) (beta : ℝ) : ℝ :=
  (pAIU H / 2) * ZAIU H beta

local notation "EAIU" => p4Q2PZ37AIU_originalTransferPartitionEnvelope

theorem p4Q2PZ37AIU_originalTransferPartitionEnvelope_pos
    (H : ℕ) (beta : ℝ) : 0 < EAIU H beta := by
  exact mul_pos (div_pos (p4Q2PZ37AHN_count_pos H) (by norm_num))
    (p4Q2PZ37AIF_originalCrossingPartition_pos H beta)

theorem p4Q2PZ37AIU_originalTransferPartitionEnvelope_eq_exp_rate
    (H : ℕ) (beta : ℝ) :
    EAIU H beta = (pAIU H / 2) * Real.exp (-(rhoAIU beta * pAIU H)) := by
  unfold p4Q2PZ37AIU_originalTransferPartitionEnvelope
  rw [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H beta]

theorem p4Q2PZ37AIU_originalTransferPartitionEnvelope_le_explicitRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    EAIU H beta ≤ (pAIU H / 2) * Real.exp (-(dAIU beta * pAIU H)) := by
  exact mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIU_originalCrossingPartition_le_explicitRate H beta hbeta)
    (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))

/-- Any fixed positive rate dominates the ORIGINAL first-degree count.
Only the scalar count sequence is compared across different volumes. -/
theorem p4Q2PZ37AIU_originalCountExp_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun H : ℕ => pAIU H * Real.exp (-(a * pAIU H)))
      atTop (𝓝 0) := by
  have hArg : Tendsto (fun H : ℕ => a * pAIU H) atTop atTop :=
    (p4Q2PZ37AIT_originalCount_tendsto_atTop).const_mul_atTop ha
  have hKernel :
      Tendsto (fun H : ℕ => (a * pAIU H) * Real.exp (-(a * pAIU H)))
        atTop (𝓝 0) := by
    simpa only [pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hArg
  have hScaled :
      Tendsto (fun H : ℕ => (1 / a) *
        ((a * pAIU H) * Real.exp (-(a * pAIU H)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hKernel.const_mul (1 / a)
  have hShape (H : ℕ) :
      (1 / a) * ((a * pAIU H) * Real.exp (-(a * pAIU H))) =
        pAIU H * Real.exp (-(a * pAIU H)) := by
    field_simp [ne_of_gt ha]
  simpa only [hShape] using hScaled

/-- Fix the positive coupling before taking the original finite-volume
index to infinity. The exact partition envelope then tends to zero. -/
theorem p4Q2PZ37AIU_originalTransferPartitionEnvelope_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => EAIU H beta) atTop (𝓝 0) := by
  have hScaled :
      Tendsto (fun H : ℕ => (1 / 2 : ℝ) *
        (pAIU H * Real.exp (-(rhoAIU beta * pAIU H)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (p4Q2PZ37AIU_originalCountExp_tendsto_zero (rhoAIU beta)
        (p4Q2PZ37AIU_originalPartitionDecayRate_pos beta hbeta)).const_mul (1 / 2 : ℝ)
  have hShape (H : ℕ) :
      EAIU H beta = (1 / 2 : ℝ) *
        (pAIU H * Real.exp (-(rhoAIU beta * pAIU H))) := by
    rw [p4Q2PZ37AIU_originalTransferPartitionEnvelope_eq_exp_rate H beta]
    ring
  simpa only [hShape] using hScaled

/-- The UNCHANGED original AIG margin has a scalar upper envelope using
the genuine partition bound and AIS's actual source-variance estimate. -/
theorem p4Q2PZ37AIU_originalNegativeMargin_le_explicitVolumeBound
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AIG_originalNegativeTransferMargin H beta ≤
      (beta / 8) * ((pAIU H) ^ 2 * Real.exp (-(2 * beta * pAIU H))) := by
  have hPartition : ZAIU H beta ≤ 1 :=
    (p4Q2PZ37AIP_originalCrossingPartition_lt_one H beta hbeta).le
  have hCoefficient : beta * ZAIU H beta ≤ beta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hPartition hbeta.le
  have hVariance := p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H
  have hVarianceNonneg : 0 ≤ VAIU H :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hProduct :
      beta * ZAIU H beta * Real.exp (-(2 * beta * pAIU H)) * VAIU H ≤
        beta * Real.exp (-(2 * beta * pAIU H)) * ((pAIU H) ^ 2 / 4) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_right hCoefficient (Real.exp_pos _).le)
      hVariance hVarianceNonneg (mul_nonneg hbeta.le (Real.exp_pos _).le)
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
  calc
    _ ≤ (beta * Real.exp (-(2 * beta * pAIU H)) * ((pAIU H) ^ 2 / 4)) / 2 :=
      div_le_div_of_nonneg_right hProduct (by norm_num)
    _ = _ := by ring

/-- The SAME original positive finite-volume margin tends to zero at each
fixed positive coupling; no replacement margin is introduced. -/
theorem p4Q2PZ37AIU_originalNegativeMargin_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => p4Q2PZ37AIG_originalNegativeTransferMargin H beta)
      atTop (𝓝 0) := by
  have hEnvelope :
      Tendsto (fun H : ℕ => (beta / 8) *
        ((pAIU H) ^ 2 * Real.exp (-(2 * beta * pAIU H)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (p4Q2PZ37AIT_originalCountSquareExp_tendsto_zero
        (2 * beta) (mul_pos (by norm_num) hbeta)).const_mul (beta / 8)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hEnvelope
    (fun H => (p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta).le)
    (fun H => p4Q2PZ37AIU_originalNegativeMargin_le_explicitVolumeBound H beta hbeta)

end PZ37AIUPartitionDecay

/-- The original spatial halfweight is at most one at nonnegative coupling,
using the nonnegative COMPLETE spatial Wilson action. -/
theorem p4Q2PZ37AIU_originalSpatialHalfweight_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (A : Cfg) :
    Real.exp (-(beta / 2) * W A) ≤ 1 := by
  have hW : 0 ≤ W A :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) A
  apply Real.exp_le_one_iff.mpr
  simpa only [neg_mul] using
    neg_nonpos.mpr (mul_nonneg (div_nonneg hbeta (by norm_num)) hW)

/-- Symmetry changes AIF's genuine right Haar integral into the left Haar
integral needed by the ORIGINAL transfer. No boundary-dependent normalization
or auxiliary Haar law is introduced. -/
theorem p4Q2PZ37AIU_originalCrossingKernel_leftHaarIntegral
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    (∫ A : Cfg, KC beta A B ∂muH) = Zcross beta := by
  calc
    (∫ A : Cfg, KC beta A B ∂muH) =
        ∫ A : Cfg, KC beta B A ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_symmetric
        H 2 (by norm_num) beta hbeta A B
    _ = Zcross beta := p4Q2PZ37AIF_originalCrossingKernel_haarIntegral H beta B

/-- AGN's exact original-source envelope survives the LEFT spatial
halfweight. This is a pointwise statement about the existing continuous
representative of the signed ZW physical source. -/
theorem p4Q2PZ37AIU_originalLeftWeightedSource_abs_le_halfCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (A : Cfg) :
    |fCont A * Real.exp (-(beta / 2) * W A)| ≤ pH / 2 := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |fCont A| * Real.exp (-(beta / 2) * W A) ≤
        (pH / 2) * Real.exp (-(beta / 2) * W A) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A)
        (Real.exp_pos _).le
    _ ≤ (pH / 2) * 1 :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIU_originalSpatialHalfweight_le_one H beta hbeta A)
        (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))
    _ = pH / 2 := mul_one _

/-- AIF's exact identity, genuine crossing Haar mass, the signed-source
envelope, and the LEFT halfweight give an all-boundary estimate while
retaining the original inverse RIGHT halfweight explicitly. -/
theorem p4Q2PZ37AIU_originalRightWeightedTransfer_abs_le_crossingEnvelope
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Real.exp ((beta / 2) * W B) * |T beta f0 B| ≤
      (pH / 2) * Zcross beta := by
  have hk := p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B
  have hDom : Integrable (fun A : Cfg => (pH / 2) * KC beta A B) muH :=
    (continuous_const.mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      |∫ A : Cfg, (fCont A * Real.exp (-(beta / 2) * W A)) *
        KC beta A B ∂muH| ≤
      ∫ A : Cfg, (pH / 2) * KC beta A B ∂muH := by
    have hNorm := norm_integral_le_of_norm_le
      (f := fun A : Cfg =>
        (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B)
      hDom (by
        filter_upwards with A
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_pos (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B)]
        exact mul_le_mul_of_nonneg_right
          (p4Q2PZ37AIU_originalLeftWeightedSource_abs_le_halfCount H beta hbeta A)
          (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le)
    simpa only [Real.norm_eq_abs] using hNorm
  calc
    Real.exp ((beta / 2) * W B) * |T beta f0 B| =
        |Real.exp ((beta / 2) * W B) * T beta f0 B| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ = |∫ A : Cfg, (fCont A * Real.exp (-(beta / 2) * W A)) *
        KC beta A B ∂muH| := by
      rw [p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral H beta B]
    _ ≤ ∫ A : Cfg, (pH / 2) * KC beta A B ∂muH := hIntegral
    _ = (pH / 2) * Zcross beta := by
      rw [integral_const_mul,
        p4Q2PZ37AIU_originalCrossingKernel_leftHaarIntegral H beta hbeta B]

/-- An explicitly retained RIGHT spatial halfweight sharpens the uniform
crossing envelope for the same ORIGINAL transfer at each boundary. -/
theorem p4Q2PZ37AIU_originalTransfer_abs_le_rightHalfweightCrossingEnvelope
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B| ≤
      Real.exp (-(beta / 2) * W B) * ((pH / 2) * Zcross beta) := by
  have hCancel :
      Real.exp (-(beta / 2) * W B) *
        Real.exp ((beta / 2) * W B) = 1 := by
    rw [← Real.exp_add]
    have hZero : -(beta / 2) * W B + (beta / 2) * W B = 0 := by ring
    rw [hZero, Real.exp_zero]
  calc
    |T beta f0 B| =
        Real.exp (-(beta / 2) * W B) *
          (Real.exp ((beta / 2) * W B) * |T beta f0 B|) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ Real.exp (-(beta / 2) * W B) * ((pH / 2) * Zcross beta) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIU_originalRightWeightedTransfer_abs_le_crossingEnvelope
          H beta hbeta B) (Real.exp_pos _).le

/-- Uniform in EVERY original boundary configuration: BOTH original spatial
halfweights and the signed ZW source remain unchanged. The estimate concerns
the actual unnormalized full-action transfer amplitude, not an operator norm
or a separately chosen scalar negative-transfer certificate. -/
theorem p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |T beta f0 B| ≤ (pH / 2) * Zcross beta := by
  have hEnvelope : 0 ≤ (pH / 2) * Zcross beta :=
    mul_nonneg (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))
      (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le
  calc
    |T beta f0 B| ≤
        Real.exp (-(beta / 2) * W B) * ((pH / 2) * Zcross beta) :=
      p4Q2PZ37AIU_originalTransfer_abs_le_rightHalfweightCrossingEnvelope
        H beta hbeta B
    _ ≤ 1 * ((pH / 2) * Zcross beta) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIU_originalSpatialHalfweight_le_one H beta hbeta B) hEnvelope
    _ = (pH / 2) * Zcross beta := one_mul _

section PZ37AIUUniformVolume

open Filter
open scoped Topology

local notation "pAIU" => p4Q2PZ37AFZ_plaquetteCount
local notation "EAIU" => p4Q2PZ37AIU_originalTransferPartitionEnvelope
local notation "rhoAIU" => p4Q2PZ37AIU_originalPartitionDecayRate
local notation "dAIU" => p4Q2PZ37AIU_explicitPartitionDecayRate
local notation "epsilonAIU" => p4Q2PZ37AIG_originalNegativeTransferMargin

/-- The exact logarithmic rate of the genuine crossing partition bounds
the actual ORIGINAL transfer, uniformly over every original boundary. -/
theorem p4Q2PZ37AIU_originalTransfer_abs_le_exactRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |decomposableOneSliceTransferIntegral H 2 beta
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B| ≤
      (pAIU H / 2) * Real.exp (-(rhoAIU beta * pAIU H)) := by
  have hBound := p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope H beta hbeta B
  rwa [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H beta] at hBound

/-- An elementary positive decay rate is available at every positive
coupling; this inequality itself also includes beta=0. -/
theorem p4Q2PZ37AIU_originalTransfer_abs_le_explicitRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |decomposableOneSliceTransferIntegral H 2 beta
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B| ≤
      (pAIU H / 2) * Real.exp (-(dAIU beta * pAIU H)) :=
  (p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope H beta hbeta B).trans
    (p4Q2PZ37AIU_originalTransferPartitionEnvelope_le_explicitRate H beta hbeta)

/-- Fix the positive ORIGINAL coupling first. Every boundary in each
sufficiently large ORIGINAL volume then has arbitrarily small transfer
amplitude. No common configuration space or operator limit is assumed. -/
theorem p4Q2PZ37AIU_originalTransfer_uniformly_small_eventually
    (beta : ℝ) (hbeta : 0 < beta) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H →
      ∀ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        |decomposableOneSliceTransferIntegral H 2 beta
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B| < eta := by
  have hEventually : ∀ᶠ H : ℕ in atTop, EAIU H beta < eta :=
    (p4Q2PZ37AIU_originalTransferPartitionEnvelope_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  exact ⟨N, fun H hH B =>
    (p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope H beta hbeta.le B).trans_lt
      (hN H hH)⟩

/-- Any dependent selection of original boundaries has scalar transfer
values tending to zero. The domains may vary with H; only the real-valued
sequence is placed in one topological space. -/
theorem p4Q2PZ37AIU_originalTransfer_boundarySequence_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta)
    (B : (H : ℕ) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Tendsto (fun H : ℕ => decomposableOneSliceTransferIntegral H 2 beta
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) (B H)) atTop (𝓝 0) := by
  have hEnvelope :=
    p4Q2PZ37AIU_originalTransferPartitionEnvelope_tendsto_zero beta hbeta
  have hLower : Tendsto (fun H : ℕ => -(EAIU H beta)) atTop (𝓝 0) := by
    simpa only [neg_zero] using hEnvelope.neg
  have hBound (H : ℕ) :
      |decomposableOneSliceTransferIntegral H 2 beta
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) (B H)| ≤ EAIU H beta :=
    p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope H beta hbeta.le (B H)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLower hEnvelope
    (fun H => (abs_le.mp (hBound H)).1)
    (fun H => (abs_le.mp (hBound H)).2)

/-- A fixed strictly positive negative depth eventually has NO original
boundary witness. The original AIG region has a varying positive margin,
so this statement does not assert that the original region becomes empty. -/
theorem p4Q2PZ37AIU_originalTransfer_fixedNegativeSublevel_eventually_empty
    (beta : ℝ) (hbeta : 0 < beta) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H →
      {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 |
        decomposableOneSliceTransferIntegral H 2 beta
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B ≤ -eta} = ∅ := by
  obtain ⟨N, hN⟩ :=
    p4Q2PZ37AIU_originalTransfer_uniformly_small_eventually beta hbeta eta heta
  refine ⟨N, fun H hH => ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro B hB
  have hNeg : decomposableOneSliceTransferIntegral H 2 beta
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B ≤ -eta := hB
  have hSmall := hN H hH B
  have hAbs := neg_le_abs (decomposableOneSliceTransferIntegral H 2 beta
    (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B)
  linarith only [hNeg, hSmall, hAbs]

/-- For the fixed original source image there is no positive amplitude
attained in every volume, even when its boundary witness may vary with H. -/
theorem p4Q2PZ37AIU_originalTransfer_no_uniformPositiveAmplitude
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ ∃ eta : ℝ, 0 < eta ∧ ∀ H : ℕ,
      ∃ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        eta ≤ |decomposableOneSliceTransferIntegral H 2 beta
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B| := by
  rintro ⟨eta, heta, hUniform⟩
  obtain ⟨N, hN⟩ :=
    p4Q2PZ37AIU_originalTransfer_uniformly_small_eventually beta hbeta eta heta
  obtain ⟨B, hB⟩ := hUniform N
  exact (not_lt_of_ge hB) (hN N le_rfl B)

/-- Negative witnesses cannot keep a volume-uniform positive depth for
this ORIGINAL unnormalized transfer and source at a fixed positive beta. -/
theorem p4Q2PZ37AIU_originalTransfer_no_uniformNegativeMargin
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ ∃ eta : ℝ, 0 < eta ∧ ∀ H : ℕ,
      ∃ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        decomposableOneSliceTransferIntegral H 2 beta
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B ≤ -eta := by
  rintro ⟨eta, heta, hUniform⟩
  apply p4Q2PZ37AIU_originalTransfer_no_uniformPositiveAmplitude beta hbeta
  refine ⟨eta, heta, fun H => ?_⟩
  obtain ⟨B, hB⟩ := hUniform H
  refine ⟨B, ?_⟩
  have hAbs := neg_le_abs (decomposableOneSliceTransferIntegral H 2 beta
    (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B)
  linarith only [hB, hAbs]

/-- The SAME original full-margin region eventually has genuine Haar
mass at least one half, while BOTH its unchanged positive margin and every
actual original-source transfer amplitude are arbitrarily small.
The common cutoff is for one fixed beta and one positive eta. -/
theorem p4Q2PZ37AIU_originalHalfHaar_with_uniformly_small_transfer
    (beta : ℝ) (hbeta : 0 < beta) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H →
      (1 / 2 : ℝ) ≤ Measure.real
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        (p4Q2PZ37AIG_originalNegativeTransferRegion H beta) ∧
      0 < epsilonAIU H beta ∧ epsilonAIU H beta < eta ∧
      ∀ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        |decomposableOneSliceTransferIntegral H 2 beta
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B| < eta := by
  obtain ⟨N₁, hN₁⟩ :=
    p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_eventually beta hbeta
  have hMargin : ∀ᶠ H : ℕ in atTop, epsilonAIU H beta < eta :=
    (p4Q2PZ37AIU_originalNegativeMargin_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hMargin
  obtain ⟨N₃, hN₃⟩ :=
    p4Q2PZ37AIU_originalTransfer_uniformly_small_eventually beta hbeta eta heta
  refine ⟨max N₁ (max N₂ N₃), fun H hH => ?_⟩
  have h₁ : N₁ ≤ H := (le_max_left _ _).trans hH
  have h₂ : N₂ ≤ H := (le_max_left N₂ N₃).trans ((le_max_right _ _).trans hH)
  have h₃ : N₃ ≤ H := (le_max_right N₂ N₃).trans ((le_max_right _ _).trans hH)
  exact ⟨hN₁ H h₁, p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta,
    hN₂ H h₂, hN₃ H h₃⟩

end PZ37AIUUniformVolume

/-- At the UNCHANGED original beta0 = log(3/2)/64, the explicit genuine
partition-decay rate has an exact rational lower bound. -/
theorem p4Q2PZ37AIU_originalFixedCoupling_explicitRate_ge_oneDiv384 :
    (1 / 384 : ℝ) ≤
      p4Q2PZ37AIU_explicitPartitionDecayRate p4Q2PZ37ADC_fixedCoupling := by
  have hInterval := p4Q2PZ37AIB_fixedCoupling_rationalInterval
  have hTangent := Real.add_one_le_exp (-2 * p4Q2PZ37ADC_fixedCoupling)
  have hExp : (1 / 2 : ℝ) ≤ Real.exp (-2 * p4Q2PZ37ADC_fixedCoupling) := by
    linarith only [hTangent, hInterval.2]
  unfold p4Q2PZ37AIU_explicitPartitionDecayRate
  calc
    (1 / 384 : ℝ) = (1 / 192 : ℝ) * (1 / 2 : ℝ) := by norm_num
    _ ≤ p4Q2PZ37ADC_fixedCoupling *
        Real.exp (-2 * p4Q2PZ37ADC_fixedCoupling) :=
      mul_le_mul hInterval.1 hExp (by norm_num)
        p4Q2PZ37ADC_fixedCoupling_pos.le

/-- Explicit cubic-volume upper envelope for the actual ORIGINAL transfer
at the unchanged fixed coupling, uniformly over EVERY original boundary.
Both original halfweights, signed ZW source and genuine Haar are retained. -/
theorem p4Q2PZ37AIU_originalFixedCoupling_transfer_abs_le_explicitVolumeBound
    (B : Cfg) :
    |T p4Q2PZ37ADC_fixedCoupling f0 B| ≤
      12 * ((H : ℝ) + 1) ^ 3 *
        Real.exp (-(((H : ℝ) + 1) ^ 3 / 16)) := by
  have hHalfCount : 0 ≤ pH / 2 :=
    div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num)
  have hDecay :
      ((H : ℝ) + 1) ^ 3 / 16 ≤
        p4Q2PZ37AIU_explicitPartitionDecayRate p4Q2PZ37ADC_fixedCoupling * pH := by
    calc
      ((H : ℝ) + 1) ^ 3 / 16 = (1 / 384 : ℝ) * pH := by
        rw [p4Q2PZ37AIB_plaquetteCount_exact H]
        ring
      _ ≤ p4Q2PZ37AIU_explicitPartitionDecayRate p4Q2PZ37ADC_fixedCoupling * pH :=
        mul_le_mul_of_nonneg_right
          p4Q2PZ37AIU_originalFixedCoupling_explicitRate_ge_oneDiv384
          (p4Q2PZ37AHN_count_pos H).le
  calc
    |T p4Q2PZ37ADC_fixedCoupling f0 B| ≤
        (pH / 2) * Zcross p4Q2PZ37ADC_fixedCoupling :=
      p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope
        H p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le B
    _ ≤ (pH / 2) * Real.exp
        (-(p4Q2PZ37AIU_explicitPartitionDecayRate p4Q2PZ37ADC_fixedCoupling * pH)) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIU_originalCrossingPartition_le_explicitRate
          H p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le) hHalfCount
    _ ≤ (pH / 2) * Real.exp (-(((H : ℝ) + 1) ^ 3 / 16)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hDecay)) hHalfCount
    _ = 12 * ((H : ℝ) + 1) ^ 3 *
        Real.exp (-(((H : ℝ) + 1) ^ 3 / 16)) := by
      rw [p4Q2PZ37AIB_plaquetteCount_exact H]
      ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Every new theorem and scalar definition has an explicit axiom audit. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalPartitionDecayRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_explicitPartitionDecayRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_explicitPartitionDecayRate_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_explicitPartitionDecayRate_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalSingleLinkPartition_eq_exp_rate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalPartitionDecayRate_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalSingleLinkPartition_le_explicitRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_explicitPartitionDecayRate_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalPartitionDecayRate_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalCrossingPartition_le_explicitRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransferPartitionEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransferPartitionEnvelope_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransferPartitionEnvelope_eq_exp_rate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransferPartitionEnvelope_le_explicitRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalCountExp_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransferPartitionEnvelope_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalNegativeMargin_le_explicitVolumeBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalNegativeMargin_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalSpatialHalfweight_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalCrossingKernel_leftHaarIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalLeftWeightedSource_abs_le_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalRightWeightedTransfer_abs_le_crossingEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_abs_le_rightHalfweightCrossingEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_abs_le_crossingEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_abs_le_exactRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_abs_le_explicitRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_uniformly_small_eventually
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_boundarySequence_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_fixedNegativeSublevel_eventually_empty
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_no_uniformPositiveAmplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalTransfer_no_uniformNegativeMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalHalfHaar_with_uniformly_small_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalFixedCoupling_explicitRate_ge_oneDiv384
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIU_originalFixedCoupling_transfer_abs_le_explicitVolumeBound
