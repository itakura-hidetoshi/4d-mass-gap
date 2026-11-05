import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExact24CenterProductErrorV5_PZ37AFY
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFZ — original FF rational intervals without receiver input

Let p_H be the length of the ORIGINAL spatial plaquette list, v_H the
ORIGINAL one-slab combinatorial volume, n_H = (v_H + 31) / 32, and
Q_H = (3/2)^n_H in Q. The fixed coupling satisfies exp(64 beta0)=3/2.

This module derives, rather than assumes, the following original bounds:
* the actual centered physical ZW source has Haar L1 mass at most p_H;
* the actual physical transfer inverse norm is at most Q_H;
* the actual one-link Perron joint half-density ratio is at most 3/2;
* the actual signed FF receiver satisfies |F_e(z,g)| <= R_H,
  where R_H = (5/2) p_H Q_H is a specified rational number.

Thus [-R_H,R_H] is a proof-carrying AFV interval at every original
boundary and every genuine SU(2) element. The AFW receiver-only input
can be constructed with NO externally supplied receiver intervals.
This uses no unknown BCF norm as a numerical constant and no dense-
rational choice of the unknown physical receiver value.

The enclosure is deliberately conservative and has midpoint ZERO.
The original AFT coefficient samples produced by it are proved zero.
It does NOT supply signed numerical receiver approximations, nonzero
Fourier certificates, a nonempty two-threshold shell, volume-uniform
coercivity, a Hamiltonian gap or a continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AFZ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFZ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFZ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFZ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFZ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "W" => p4Q2JU_originalSpatialWilsonPhysicalSource H
local notation "Wc" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "L" => ContinuousMap.toLp 2 muH ℝ
/-- Actual finite-volume spatial Wilson plaquette count as a real number.
Use a named definition: the pinned Lean syntax quotation precheck does not
support dot projection inside a local-notation expansion. -/
def p4Q2PZ37AFZ_plaquetteCount (H : ℕ) : ℝ :=
  ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℝ)
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "vH" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "Tnorm" => ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num) b0 hb0‖
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters

local instance p4Q2PZ37AFZ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFZ_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Integer rounding of the actual finite Wilson action budget. -/
def p4Q2PZ37AFZ_normExponent : ℕ := (vH + 31) / 32

/-- Explicit rational, not a choice depending on an unknown eigenvector. -/
def p4Q2PZ37AFZ_rationalInverseNorm : ℚ :=
  (3 / 2 : ℚ) ^ p4Q2PZ37AFZ_normExponent H

/-- Explicit rational envelope of the original FF response. -/
def p4Q2PZ37AFZ_rationalReceiverBound : ℚ :=
  (5 / 2 : ℚ) * (periodicHypercubicEvenSpatialSlicePlaquetteList H).length *
    p4Q2PZ37AFZ_rationalInverseNorm H

local notation "QH" => p4Q2PZ37AFZ_rationalInverseNorm H
local notation "RH" => p4Q2PZ37AFZ_rationalReceiverBound H

/-- The original physical centering scalar, unchanged from ZW. -/
def p4Q2PZ37AFZ_originalWilsonMean : ℝ := inner ℝ W U
local notation "mH" => p4Q2PZ37AFZ_originalWilsonMean H

def p4Q2PZ37AFZ_originalCenteredContinuous : C(Cfg, ℝ) :=
  (1 / 2 : ℝ) • (Wc - mH • (1 : C(Cfg, ℝ)))

/-- Identify the actual physical Hilbert centering with actual Haar mean. -/
theorem p4Q2PZ37AFZ_originalWilsonMean_eq_integral :
    mH = ∫ A : Cfg, Wc A ∂muH := by
  have hU : (fun A : Cfg => (U : Lp ℝ 2 muH) A) =ᵐ[muH]
      (fun _ => (1 : ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 muH (1 : ℝ)) A) =ᵐ[muH] _
    exact Lp.coeFn_const (μ := muH) (p := 2) (c := (1 : ℝ))
  change inner ℝ (W : Lp ℝ 2 muH) (U : Lp ℝ 2 muH) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [p4Q2JU_originalSpatialWilsonPhysicalSource_ae H, hU] with A hW hOne
  -- In pinned mathlib the scalar real inner product is defined via RCLike.re;
  -- rewrite it BEFORE simplifying the coercions of the physical Lp unit.
  change inner ℝ ((W : Lp ℝ 2 muH) A) ((U : Lp ℝ 2 muH) A) = Wc A
  calc
    inner ℝ ((W : Lp ℝ 2 muH) A) ((U : Lp ℝ 2 muH) A) =
        ((U : Lp ℝ 2 muH) A) * ((W : Lp ℝ 2 muH) A) := by
          simp only [real_inner_eq_re_inner (𝕜 := ℝ),
            RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
    _ = Wc A := by
      rw [hOne, hW]
      ring

/-- The original action and its actual mean are in the same finite range. -/
theorem p4Q2PZ37AFZ_originalWilsonMean_bounds :
    0 ≤ mH ∧ mH ≤ 2 * pH := by
  have hInt : Integrable (fun A : Cfg => Wc A) muH :=
    ((Lp.memLp (W : Lp ℝ 2 muH)).integrable (by norm_num)).congr
      (p4Q2JU_originalSpatialWilsonPhysicalSource_ae H)
  rw [p4Q2PZ37AFZ_originalWilsonMean_eq_integral]
  constructor
  · apply integral_nonneg
    intro A
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) A
  · calc
      (∫ A : Cfg, Wc A ∂muH) ≤ ∫ _ : Cfg, 2 * pH ∂muH := by
        apply integral_mono hInt (integrable_const _)
        intro A
        exact periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
          H 2 (by norm_num) A
      _ = 2 * pH := by simp

/-- The true Gauss-law source is the same continuous centered action in L2. -/
theorem p4Q2PZ37AFZ_originalCenteredSource_eq_toLp :
    (f0 : Lp ℝ 2 muH) = L (p4Q2PZ37AFZ_originalCenteredContinuous H) := by
  change (1 / 2 : ℝ) • ((W : Lp ℝ 2 muH) - mH • (U : Lp ℝ 2 muH)) =
    L ((1 / 2 : ℝ) • (Wc - mH • (1 : C(Cfg, ℝ))))
  rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp, map_smul, map_sub, map_smul]

/-- No pointwise fiction for an L2 representative: the bound is Haar-a.e. -/
theorem p4Q2PZ37AFZ_originalCenteredSource_abs_le_ae :
    ∀ᵐ A : Cfg ∂muH, |(f0 : Lp ℝ 2 muH) A| ≤ pH := by
  have hRep : (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH]
      (p4Q2PZ37AFZ_originalCenteredContinuous H) := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) (p4Q2PZ37AFZ_originalCenteredContinuous H)
  obtain ⟨hm0, hm1⟩ := p4Q2PZ37AFZ_originalWilsonMean_bounds H
  filter_upwards [hRep] with A hA
  rw [hA]
  change |(1 / 2 : ℝ) * (Wc A - mH * 1)| ≤ pH
  have hW0 : 0 ≤ Wc A :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg H 2 (by norm_num) A
  have hW1 : Wc A ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) A
  apply abs_le.mpr
  constructor <;> linarith only [hm0, hm1, hW0, hW1]

/-- Concrete source budget from the original plaquette count; no source oracle. -/
theorem p4Q2PZ37AFZ_originalCenteredSource_L1_le_plaquetteCount :
    Msrc ≤ pH := by
  have hf : Integrable (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hAbs : Integrable (fun A : Cfg => |(f0 : Lp ℝ 2 muH) A|) muH := by
    simpa only [Real.norm_eq_abs] using hf.norm
  unfold p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass
  calc
    (∫ A : Cfg, |(f0 : Lp ℝ 2 muH) A| ∂muH) ≤ ∫ _ : Cfg, pH ∂muH :=
      integral_mono_ae hAbs (integrable_const _)
        (p4Q2PZ37AFZ_originalCenteredSource_abs_le_ae H)
    _ = pH := by simp

/-- Integrate the actual Wilson kernel (0<K<=1) against the signed source. -/
theorem p4Q2PZ37AFZ_originalTransfer_abs_le_plaquetteCount (B : Cfg) :
    |t B| ≤ pH := by
  let f : Cfg → ℝ := fun A => (f0 : Lp ℝ 2 muH) A
  have hf : Integrable f muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hInt : Integrable (fun A : Cfg => f A * K A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) b0 hb0 (f0 : Lp ℝ 2 muH) B
  have hK (A : Cfg) : |K A B - 0| ≤ (1 : ℝ) := by
    rw [sub_zero, abs_of_pos
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H 2 b0 A B)]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
      H 2 (by norm_num) b0 hb0 A B
  have h := p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    muH f (fun A => K A B) (fun _ => 0) 1 hf hInt (by simp) hK
  have hMass : |t B| ≤ Msrc := by
    rw [p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral]
    simpa only [f, p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass,
      mul_zero, integral_zero, sub_zero, one_mul] using h
  exact hMass.trans (p4Q2PZ37AFZ_originalCenteredSource_L1_le_plaquetteCount H)

theorem p4Q2PZ37AFZ_rationalInverseNorm_pos : 0 < QH := by
  unfold p4Q2PZ37AFZ_rationalInverseNorm
  positivity

/-- The original physical transfer inverse norm has a specified rational bound.
The exponent ceiling loses at most one factor 3/2 from the Wilson action floor. -/
theorem p4Q2PZ37AFZ_originalInverseNorm_le_rational :
    Tnorm⁻¹ ≤ (QH : ℝ) := by
  let n := p4Q2PZ37AFZ_normExponent H
  have hNat : vH ≤ 32 * n := by
    dsimp [n, p4Q2PZ37AFZ_normExponent]
    omega
  have hReal : (vH : ℝ) ≤ 32 * (n : ℝ) := by exact_mod_cast hNat
  have hScale :
      b0 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H ≤
        (n : ℝ) * (64 * b0) := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    have h := mul_le_mul_of_nonneg_left hReal hb0
    nlinarith only [h]
  calc
    Tnorm⁻¹ ≤ Real.exp
        (b0 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) :=
      p4Q2PZ37AEJ_originalPhysicalTransfer_inverseNorm_le_expAction
        H 2 (by norm_num) b0 hb0
    _ ≤ Real.exp ((n : ℝ) * (64 * b0)) := Real.exp_le_exp.mpr hScale
    _ = (3 / 2 : ℝ) ^ n := by
      rw [Real.exp_nat_mul, p4Q2PZ37ADC_fixedCoupling_exp_eq]
    _ = (QH : ℝ) := by
      simp [p4Q2PZ37AFZ_rationalInverseNorm, n]

/-- Exact fixed-coupling identity gives a rational one-link Harnack majorant. -/
theorem p4Q2PZ37AFZ_oneLinkHarnackFactor_le_rational :
    Real.exp (8 * b0) ≤ (3 / 2 : ℝ) := by
  calc
    Real.exp (8 * b0) ≤ Real.exp (64 * b0) :=
      Real.exp_le_exp.mpr (by nlinarith only [hb0])
    _ = (3 / 2 : ℝ) := p4Q2PZ37ADC_fixedCoupling_exp_eq

/-- Ratio of the SAME genuine half-densities, not an absolute density oracle. -/
theorem p4Q2PZ37AFZ_originalDensityRatio_bounds
    (e : Link) (z : Pair) (g : G) :
    0 ≤ rho z / rho (z.1, Function.update z.2 e g) ∧
      rho z / rho (z.1, Function.update z.2 e g) ≤ (3 / 2 : ℝ) := by
  have hPos := continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0
    (z.1, Function.update z.2 e g)
  have hComp := p4Q2PZ37AEL_originalSqrtDensity_oneLinkHarnack
    H z.1 z.2 e (z.2 e) g
  change rho (z.1, Function.update z.2 e (z.2 e)) ≤
    Real.exp (8 * b0) * rho (z.1, Function.update z.2 e g) at hComp
  simp only [Function.update_eq_self] at hComp
  constructor
  · exact div_nonneg
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z).le hPos.le
  · apply (div_le_iff₀ hPos).2
    exact hComp.trans (mul_le_mul_of_nonneg_right
      p4Q2PZ37AFZ_oneLinkHarnackFactor_le_rational hPos.le)

/-- Exact cancellation is carried out only inside the original FF formula. -/
theorem p4Q2PZ37AFZ_originalFF_eq_densityRatioTransfer
    (e : Link) (z : Pair) (g : G) :
    F e z g = Tnorm⁻¹ * (t z.2 -
      (rho z / rho (z.1, Function.update z.2 e g)) *
        t (Function.update z.2 e g)) := by
  rw [p4Q2PZ37AFM_originalFF_eq_affineTransferSection]
  unfold p4Q2PZ37ABZ_originalTransferSectionPrefactor
    p4Q2PZ37ABZ_originalTransferSection
  ring

/-- Unconditional finite-volume rational enclosure of the actual FF receiver. -/
theorem p4Q2PZ37AFZ_originalFF_abs_le_rational
    (e : Link) (z : Pair) (g : G) : |F e z g| ≤ (RH : ℝ) := by
  let r := rho z / rho (z.1, Function.update z.2 e g)
  obtain ⟨hr0, hr1⟩ := p4Q2PZ37AFZ_originalDensityRatio_bounds H e z g
  have hP : 0 ≤ pH := Nat.cast_nonneg _
  have ht0 : 0 ≤ Tnorm⁻¹ :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) b0 hb0)).le
  have hTerm : |t z.2 - r * t (Function.update z.2 e g)| ≤ (5 / 2 : ℝ) * pH := by
    calc
      |t z.2 - r * t (Function.update z.2 e g)| ≤
          |t z.2| + |r * t (Function.update z.2 e g)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (t z.2) (-(r * t (Function.update z.2 e g))))
      _ = |t z.2| + r * |t (Function.update z.2 e g)| := by
        rw [abs_mul, abs_of_nonneg hr0]
      _ ≤ pH + r * pH := add_le_add
        (p4Q2PZ37AFZ_originalTransfer_abs_le_plaquetteCount H z.2)
        (mul_le_mul_of_nonneg_left
          (p4Q2PZ37AFZ_originalTransfer_abs_le_plaquetteCount H
            (Function.update z.2 e g)) hr0)
      _ ≤ pH + (3 / 2 : ℝ) * pH :=
        add_le_add_left (mul_le_mul_of_nonneg_right hr1 hP) pH
      _ = (5 / 2 : ℝ) * pH := by ring
  rw [p4Q2PZ37AFZ_originalFF_eq_densityRatioTransfer, abs_mul, abs_of_nonneg ht0]
  calc
    Tnorm⁻¹ * |t z.2 - r * t (Function.update z.2 e g)| ≤
        Tnorm⁻¹ * ((5 / 2 : ℝ) * pH) := mul_le_mul_of_nonneg_left hTerm ht0
    _ ≤ (QH : ℝ) * ((5 / 2 : ℝ) * pH) :=
      mul_le_mul_of_nonneg_right (p4Q2PZ37AFZ_originalInverseNorm_le_rational H)
        (mul_nonneg (by norm_num) hP)
    _ = (RH : ℝ) := by
      unfold p4Q2PZ37AFZ_rationalReceiverBound
      push_cast
      ring

/-- The unchanged right link is an exact zero, independent of Perron numerics. -/
theorem p4Q2PZ37AFZ_originalFF_ownLink_zero (e : Link) (z : Pair) :
    F e z (z.2 e) = 0 := by
  rw [p4Q2PZ37AFZ_originalFF_eq_densityRatioTransfer]
  have hr : rho z ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z).ne'
  simp only [Function.update_eq_self, div_self hr, one_mul, sub_self, mul_zero]

/-- No receiver interval is supplied: both rational endpoints and inclusion
follow from the original action, signed source, transfer and Perron bounds. -/
def p4Q2PZ37AFZ_originalReceiverRationalInterval
    (e : Link) (z : Pair) (g : G) : p4Q2PZ37AFV_verifiedInterval (F e z g) where
  lower := -RH
  upper := RH
  hLower := by
    have h := (abs_le.mp (p4Q2PZ37AFZ_originalFF_abs_le_rational H e z g)).1
    simpa only [Rat.cast_neg] using h
  hUpper := (abs_le.mp (p4Q2PZ37AFZ_originalFF_abs_le_rational H e z g)).2

/-- Explicitly expose the conservative zero midpoint; no signed value is inferred. -/
theorem p4Q2PZ37AFZ_originalReceiverBall_sample_zero
    (e : Link) (z : Pair) (g : G) :
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFZ_originalReceiverRationalInterval H e z g)).sample = 0 := by
  simp [p4Q2PZ37AFV_intervalToBall, p4Q2PZ37AFZ_originalReceiverRationalInterval]

theorem p4Q2PZ37AFZ_originalReceiverBall_error_rational
    (e : Link) (z : Pair) (g : G) :
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFZ_originalReceiverRationalInterval H e z g)).error = (RH : ℝ) := by
  change (((RH - (-RH) : ℚ) : ℝ) / 2) = (RH : ℝ)
  push_cast
  ring

/-- Construct AFW's original 24-center physical interval input without an
external receiver/Perron/transfer interval parameter. -/
def p4Q2PZ37AFZ_originalReceiverIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) :
    p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c where
  receiver := fun a _ i =>
    p4Q2PZ37AFZ_originalReceiverRationalInterval H e a (gridCenter i)

/-- Preserve the original AFX -> AFV -> AFT -> AFI physical certificate. -/
def p4Q2PZ37AFZ_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) (hlo : 0 ≤ lo) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFX_toOriginalCoefficientVariance H e c hlo
    (p4Q2PZ37AFZ_originalReceiverIntervals H e c)

/-- Scope is itself checkable: this baseline produces ZERO rational Fourier
centers, not a nonzero physical coefficient certificate. -/
theorem p4Q2PZ37AFZ_originalAFT_coefficientSamples_zero
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (a : Pair) (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    (p4Q2PZ37AFX_toOriginalVerifiedSamples H e c
      (p4Q2PZ37AFZ_originalReceiverIntervals H e c)).coefficientSample a j i = 0 := by
  by_cases ha : a ∈ c.s
  · rw [p4Q2PZ37AFY_originalAFT_coefficientSample_exact H e c
      (p4Q2PZ37AFZ_originalReceiverIntervals H e c) a ha j i]
    change (((-RH + RH) / 2 : ℚ) * p4Q2PZ37AFX_exactRationalCharacter j i) = 0
    ring
  · simp only [p4Q2PZ37AFX_toOriginalVerifiedSamples,
      p4Q2PZ37AFV_toOriginalVerifiedSamples, dif_neg ha]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalWilsonMean_eq_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalWilsonMean_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalCenteredSource_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalCenteredSource_abs_le_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalCenteredSource_L1_le_plaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalTransfer_abs_le_plaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_rationalInverseNorm_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalInverseNorm_le_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_oneLinkHarnackFactor_le_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalDensityRatio_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalFF_eq_densityRatioTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalFF_abs_le_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalFF_ownLink_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalReceiverRationalInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalReceiverBall_sample_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalReceiverBall_error_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalReceiverIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_toOriginalCoefficientVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFZ_originalAFT_coefficientSamples_zero
