import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedFactorIntervalsV5_PZ37AGA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGB — genuine centered source cancels the constant Wilson kernel

AGA reduced true signed FF receiver sign certification to the actual
signed one-slab transfer integrals and original Perron ratio. AFZ gave
the conservative |t_H(B)| <= p_H bound, with p_H the literal spatial
Wilson plaquette-list length.

AGB proves that the ORIGINAL ZW Gauss-law-centered physical source has
Haar integral exactly ZERO (using its actual continuous representative,
not an invented source). Consequently for any REAL constant c,

 t_H(B) = ∫ f_H(A) * (K_H(A,B) - c) dmu_H(A).

The same true Wilson kernel satisfies k_H <= K_H(A,B) <= 1, with
k_H = exp(-beta0 * originalOneSlabActionBudget H) > 0.
Choosing c=(1+k_H)/2 yields

 |t_H(B)| <= ((1-k_H)/2) * Msrc_H <= p_H/2.

The second bound is an unconditional RATIONAL radius derived from
original centered Gauss-law source, Perron transfer, and Haar.
It yields a genuine AFV rational interval [-p_H/2,p_H/2] for both
unupdated and actual updated signed transfer integrals, feeding AGA's
unchanged 24-center original FF coefficient certificate without any
external receiver/transfer interval oracle.

The resulting intervals have midpoint ZERO. In particular AGB
DOES NOT certify nonzero signed transfer samples, a nonempty two-sign
physical shell, volume-uniform coercivity, any Hamiltonian spectral
gap or the continuum 4D Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "W" =>
  p4Q2JU_originalSpatialWilsonPhysicalSource H
local notation "Wc" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "mH" => p4Q2PZ37AFZ_originalWilsonMean H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" =>
  p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" =>
  decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters

local instance p4Q2PZ37AGB_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGB_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The authentic ZW centered physical Haar-L2 vector has EXACTLY zero
Haar expectation. Its representative is identified Haar-a.e. with the
continuous original spatial Wilson action minus its genuine Haar mean. -/
theorem p4Q2PZ37AGB_originalCenteredSource_HaarMean_zero :
    (∫ A : Cfg, (f0 : Lp ℝ 2 muH) A ∂muH) = 0 := by
  have hWInt : Integrable (fun A : Cfg => Wc A) muH :=
    ((Lp.memLp (W : Lp ℝ 2 muH)).integrable (by norm_num)).congr
      (p4Q2JU_originalSpatialWilsonPhysicalSource_ae H)
  have hRep :
      (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH]
      (fun A : Cfg => (1 / 2 : ℝ) * (Wc A - mH)) := by
    have hRepRaw :
        (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH]
        (p4Q2PZ37AFZ_originalCenteredContinuous H) := by
      rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
      exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
        (μ := muH) (p4Q2PZ37AFZ_originalCenteredContinuous H)
    filter_upwards [hRepRaw] with A hA
    rw [hA]
    change (1 / 2 : ℝ) * (Wc A - mH * 1) =
      (1 / 2 : ℝ) * (Wc A - mH)
    ring
  calc
    (∫ A : Cfg, (f0 : Lp ℝ 2 muH) A ∂muH) =
        ∫ A : Cfg, (1 / 2 : ℝ) * (Wc A - mH) ∂muH :=
      integral_congr_ae hRep
    _ = (1 / 2 : ℝ) * ((∫ A : Cfg, Wc A ∂muH) - mH) := by
      rw [integral_const_mul]
      rw [integral_sub hWInt (integrable_const _)]
      simp
    _ = 0 := by
      rw [← p4Q2PZ37AFZ_originalWilsonMean_eq_integral H]
      ring

/-- The original signed transfer is invariant under subtracting ANY
constant kernel baseline, because the actual physical source has
zero Haar mean. No altered transfer operator or new posterior. -/
theorem p4Q2PZ37AGB_originalTransfer_eq_kernelCenteredIntegral
    (B : Cfg) (c : ℝ) :
    t B = ∫ A : Cfg,
      (f0 : Lp ℝ 2 muH) A * (K A B - c) ∂muH := by
  let f : Cfg → ℝ := fun A => (f0 : Lp ℝ 2 muH) A
  have hf : Integrable f muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hu : Integrable (fun A : Cfg => f A * K A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) b0 hb0 (f0 : Lp ℝ 2 muH) B
  have hv : Integrable (fun A : Cfg => f A * c) muH :=
    hf.mul_const c
  have hzero : (∫ A : Cfg, f A * c ∂muH) = 0 := by
    rw [integral_mul_const, p4Q2PZ37AGB_originalCenteredSource_HaarMean_zero H]
    ring
  rw [p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral]
  calc
    (∫ A : Cfg, f A * K A B ∂muH) =
        ∫ A : Cfg, (f A * K A B - f A * c) ∂muH := by
      rw [integral_sub hu hv, hzero, sub_zero]
    _ = ∫ A : Cfg, f A * (K A B - c) ∂muH := by
      congr 1
      funext A
      ring

/-- This is the genuine action floor and ceiling, not an independently
invented compact-group norm or Haar envelope. -/
theorem p4Q2PZ37AGB_originalKernel_centeredMidpointBound
    (A B : Cfg) :
    |K A B - (1 + k) / 2| ≤ (1 - k) / 2 := by
  have hLow : k ≤ K A B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
      H 2 (by norm_num) b0 hb0 A B
  have hHigh : K A B ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
      H 2 (by norm_num) b0 hb0 A B
  apply abs_le.mpr
  constructor <;> linarith only [hLow, hHigh]

theorem p4Q2PZ37AGB_originalKernel_radius_nonneg :
    0 ≤ (1 - k) / 2 := by
  have hk : k ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_one
      H b0 hb0
  linarith only [hk]

/-- No external modulus: apply AEV's existing signed kernel integral
variation inequality to the ACTUAL centered source and true Wilson
kernel, with the optimal midpoint of the global [k,1] kernel interval. -/
theorem p4Q2PZ37AGB_originalTransfer_abs_le_centeredActionFloor
    (B : Cfg) :
    |t B| ≤ ((1 - k) / 2) * Msrc := by
  let f : Cfg → ℝ := fun A => (f0 : Lp ℝ 2 muH) A
  let c : ℝ := (1 + k) / 2
  let E : ℝ := (1 - k) / 2
  have hf : Integrable f muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hu : Integrable (fun A : Cfg => f A * K A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) b0 hb0 (f0 : Lp ℝ 2 muH) B
  have hv : Integrable (fun A : Cfg => f A * c) muH :=
    hf.mul_const c
  have hConstant : (∫ A : Cfg, f A * c ∂muH) = 0 := by
    rw [integral_mul_const, p4Q2PZ37AGB_originalCenteredSource_HaarMean_zero H]
    ring
  have hK (A : Cfg) : |K A B - c| ≤ E :=
    p4Q2PZ37AGB_originalKernel_centeredMidpointBound H A B
  have h := p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    muH f (fun A : Cfg => K A B) (fun _ => c) E hf hu hv hK
  rw [hConstant, sub_zero] at h
  rw [p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral]
  simpa only [f, E, p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass] using h

/-- Stronger than AFZ's p_H bound: only half the genuine source mass
contributes because its Haar mean vanishes and Wilson 0<k<=K<=1. -/
theorem p4Q2PZ37AGB_originalTransfer_abs_le_halfPlaquetteCount
    (B : Cfg) :
    |t B| ≤ pH / 2 := by
  have h0 : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hk0 : 0 ≤ k :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H b0).le
  have hE : 0 ≤ (1 - k) / 2 :=
    p4Q2PZ37AGB_originalKernel_radius_nonneg H
  have hEle : (1 - k) / 2 ≤ (1 / 2 : ℝ) := by
    linarith only [hk0]
  calc
    |t B| ≤ ((1 - k) / 2) * Msrc :=
      p4Q2PZ37AGB_originalTransfer_abs_le_centeredActionFloor H B
    _ ≤ ((1 - k) / 2) * pH :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AFZ_originalCenteredSource_L1_le_plaquetteCount H) hE
    _ ≤ (1 / 2 : ℝ) * pH :=
      mul_le_mul_of_nonneg_right hEle h0
    _ = pH / 2 := by ring

/-- Actual integer plaquette count determines a concrete rational
transfer interval radius, with no ad hoc physical approximation. -/
def p4Q2PZ37AGB_rationalTransferRadius (H : ℕ) : ℚ :=
  ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℚ) / 2

theorem p4Q2PZ37AGB_rationalTransferRadius_real_eq :
    ((p4Q2PZ37AGB_rationalTransferRadius H : ℚ) : ℝ) = pH / 2 := by
  unfold p4Q2PZ37AGB_rationalTransferRadius p4Q2PZ37AFZ_plaquetteCount
  push_cast
  ring

/-- Genuine zero-centered rational interval for the original SIGNED
transfer at any actual spatial boundary; no presumed interval input. -/
def p4Q2PZ37AGB_originalTransferRationalInterval
    (B : Cfg) :
    p4Q2PZ37AFV_verifiedInterval (t B) where
  lower := -(p4Q2PZ37AGB_rationalTransferRadius H)
  upper := p4Q2PZ37AGB_rationalTransferRadius H
  hLower := by
    have h := (abs_le.mp
      (p4Q2PZ37AGB_originalTransfer_abs_le_halfPlaquetteCount H B)).1
    simpa only [Rat.cast_neg, p4Q2PZ37AGB_rationalTransferRadius_real_eq H] using h
  hUpper := by
    have h := (abs_le.mp
      (p4Q2PZ37AGB_originalTransfer_abs_le_halfPlaquetteCount H B)).2
    simpa only [p4Q2PZ37AGB_rationalTransferRadius_real_eq H] using h

/-- Discharge AGA's original signed transfer-only data requirements
with genuine finite-volume rational intervals (but zero centers). -/
def p4Q2PZ37AGB_originalAutomaticTransferOnlyIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) :
    p4Q2PZ37AGA_originalTransferOnlyIntervals H e lo hi c where
  unupdatedTransfer := fun z _ =>
    p4Q2PZ37AGB_originalTransferRationalInterval H z.2
  updatedTransfer := fun z _ i =>
    p4Q2PZ37AGB_originalTransferRationalInterval H
      (Function.update z.2 e (gridCenter i))

/-- The original AGA factor interval construction and AFX exact
24-center character certificate can be instantiated with NO external
receiver, transfer-integral, norm, or Perron-ratio interval input. -/
noncomputable def p4Q2PZ37AGB_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AGA_transferOnly_toOriginalCoefficientVariance H e c hlo
    (p4Q2PZ37AGB_originalAutomaticTransferOnlyIntervals H e c)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalCenteredSource_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalTransfer_eq_kernelCenteredIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalKernel_centeredMidpointBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalKernel_radius_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalTransfer_abs_le_centeredActionFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalTransfer_abs_le_halfPlaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_rationalTransferRadius_real_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalTransferRationalInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_originalAutomaticTransferOnlyIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGB_toOriginalCoefficientVariance
