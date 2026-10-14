import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalExpectationGapDetectionNullLocusV5_GM
import Mathlib.Tactic

/-!
# P4-Q2-GN: original Wilson transfer-fiber detector and exact kernel criteria

Write L = ||T_beta||^(-1), s(z) = sqrt(rho_beta(z)), and
  t_f(B) = integral K_beta(A,B) f(A) dHaar(A).
The original continuous receiver is exactly L^2 t_f(B) / s(A,B).
Its FF normalization weight is L / s(A,B): the positive continuous
vacuum cancels, but the genuine joint density DOES NOT disappear.

The difference d of the two genuine normalized Wilson posterior
probability densities has Haar integral zero. Thus GI's detector is
  Delta_f(z) = -L s(z) J_f(z),
  J_f(z) = integral t_f(B[e:=g]) / s(A,B[e:=g]) d_beta,e,B(g) dHaar(g).
This is an exact formula for the ORIGINAL Wilson transfer acting on the
ORIGINAL physical source, not a postulated nondegenerate frame.

Since L and s are strictly positive, its pointwise and a.e. kernel is
exactly J=0. Prove automatic fiber integrability, transfer-kernel
containment, and instantiate the true fine right Krylov and left
three-mode sources while keeping frozen beta(n) distinct from fine
beta(n+1). Import GM and connect its exact GL gap-square null locus.
No actual signed Krylov detector injectivity, positive minimum
eigenvalue, volume uniformity, H1-C3 closure, or continuum gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2GN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2GN_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μ" => normalizedCompactHaar Gauge
local notation "L" => (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
  H 2 (by norm_num) beta hbeta‖⁻¹)
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) beta hbeta
local notation "D" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H beta hbeta

/-- Continuity is for the actual interacting posterior density contrast. -/
theorem p4Q2GN_originalDensityContrast_continuous (B : Cfg) (e : Link) :
    Continuous (D B e) := by
  let L0 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) B e
  let L1 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) B e
  have h0 : Continuous L0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) B e
  have h1 : Continuous L1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) B e
  exact (continuous_continuousNormalizedExp μ L0 h0).sub
    (continuous_continuousNormalizedExp μ L1 h1)

/-- Both genuine Wilson posterior laws have mass one; their density
contrast has zero Haar mean. No independent-Haar posterior is introduced. -/
theorem p4Q2GN_originalDensityContrast_integral_zero (B : Cfg) (e : Link) :
    (∫ g, D B e g ∂μ) = 0 := by
  let L0 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) B e
  let L1 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) B e
  have hc0 : Continuous L0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) B e
  have hc1 : Continuous L1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) B e
  -- Local notation μ does not support field projection: name the Haar measure.
  let ν : Measure Gauge := normalizedCompactHaar Gauge
  have hIntExp0 : Integrable (fun g : Gauge => Real.exp (L0 g)) ν :=
    (Real.continuous_exp.comp hc0).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntExp1 : Integrable (fun g : Gauge => Real.exp (L1 g)) ν :=
    (Real.continuous_exp.comp hc1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  haveI : IsProbabilityMeasure (ν.tilted L0) :=
    isProbabilityMeasure_tilted hIntExp0
  haveI : IsProbabilityMeasure (ν.tilted L1) :=
    isProbabilityMeasure_tilted hIntExp1
  have hi0 : Integrable (continuousNormalizedExp μ L0) μ :=
    (continuous_continuousNormalizedExp μ L0 hc0).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (continuousNormalizedExp μ L1) μ :=
    (continuous_continuousNormalizedExp μ L1 hc1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn0 : (∫ g, continuousNormalizedExp μ L0 g ∂μ) = 1 := by
    have h : (∫ _g : Gauge, (1 : ℝ) ∂(ν.tilted L0)) = 1 := by simp
    rw [integral_tilted] at h
    simpa only [smul_eq_mul, mul_one] using h
  have hn1 : (∫ g, continuousNormalizedExp μ L1 g ∂μ) = 1 := by
    have h : (∫ _g : Gauge, (1 : ℝ) ∂(ν.tilted L1)) = 1 := by simp
    rw [integral_tilted] at h
    simpa only [smul_eq_mul, mul_one] using h
  change (∫ g, continuousNormalizedExp μ L0 g - continuousNormalizedExp μ L1 g ∂μ) = 0
  rw [integral_sub hi0 hi1, hn0, hn1, sub_self]

/-- Cancel only the actual positive vacuum in the FF normalization. -/
theorem p4Q2GN_originalDensityCancellationWeight_eq (z : Cfg × Cfg) :
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num) beta hbeta z *
      normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num) beta hbeta z.2 =
    L / s z := by
  let omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta z.2
  have ho : omega ≠ 0 := (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
    H 2 (by norm_num) beta hbeta z.2).ne'
  have hs : s z ≠ 0 := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta z).ne'
  change ((L * omega) / s z) * omega⁻¹ = L / s z
  field_simp [ho, hs]

/-- Original receiver expressed directly through the genuine Wilson
kernel integral of the physical source, not an arbitrary finite vector. -/
theorem p4Q2GN_originalReceiver_eq_transferIntegral (f : Phys) (z : Cfg × Cfg) :
    normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) beta hbeta f z =
    L ^ 2 * decomposableOneSliceTransferIntegral H 2 beta f z.2 / s z := by
  let omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta z.2
  have ho : omega ≠ 0 := (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
    H 2 (by norm_num) beta hbeta z.2).ne'
  have hs : s z ≠ 0 := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta z).ne'
  change ((L * omega) / s z) *
    (L * decomposableOneSliceTransferIntegral H 2 beta f z.2 / omega) = _
  field_simp [ho, hs]

/-- Source dependence of the full signed response, including update drift. -/
theorem p4Q2GN_originalSignedResponse_eq_transferDifference
    (f : Phys) (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e (z,g) =
    L * (decomposableOneSliceTransferIntegral H 2 beta f z.2 -
      s z / s (z.1, Function.update z.2 e g) *
        decomposableOneSliceTransferIntegral H 2 beta f (Function.update z.2 e g)) := by
  classical
  have hL : L ≠ 0 := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta)).ne'
  have hs := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta z).ne'
  have hs' := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta
    (z.1, Function.update z.2 e g)).ne'
  rw [p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_apply,
    p4Q2GN_originalReceiver_eq_transferIntegral,
    p4Q2GN_originalReceiver_eq_transferIntegral,
    p4Q2GN_originalDensityCancellationWeight_eq]
  field_simp [hL, hs, hs']

/-- The remaining original transfer-fiber moment. All density factors
are the true frozen Wilson factors; the source retains its physical type. -/
noncomputable def p4Q2GN_originalTransferFiberContrastMoment
    (f : Phys) (e : Link) (z : Cfg × Cfg) : ℝ := by
  classical
  exact ∫ g : Gauge,
    (decomposableOneSliceTransferIntegral H 2 beta f (Function.update z.2 e g) /
      s (z.1, Function.update z.2 e g)) * D z.2 e g ∂μ

/-- No default-zero nonintegrable integral is used in the kernel formula. -/
theorem p4Q2GN_originalTransferFiberContrast_integrable
    (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Integrable (fun g : Gauge =>
      (decomposableOneSliceTransferIntegral H 2 beta f (Function.update z.2 e g) /
        s (z.1, Function.update z.2 e g)) * D z.2 e g) μ := by
  classical
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) beta hbeta f
  have hUp : Continuous (fun g : Gauge => (z.1, Function.update z.2 e g)) := by fun_prop
  have hi : Integrable (fun g => O (z.1, Function.update z.2 e g) * D z.2 e g) μ :=
    ((O.continuous.comp hUp).mul (p4Q2GN_originalDensityContrast_continuous H beta hbeta z.2 e)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hL : L ≠ 0 := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta)).ne'
  apply (hi.div_const (L ^ 2)).congr
  filter_upwards with g
  dsimp [O]
  rw [p4Q2GN_originalReceiver_eq_transferIntegral]
  have hs := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta
    (z.1, Function.update z.2 e g)).ne'
  apply (div_eq_iff (pow_ne_zero 2 hL)).2
  ring

/-- The unupdated receiver cancels because both original posterior laws
have mass one. The updated receiver and its actual weight remain. -/
theorem p4Q2GN_originalExpectationGap_eq_updatedReceiverContrast
    (f : Phys) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H beta hbeta f e z =
    -(∫ g : Gauge,
      normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) beta hbeta f
        (z.1, Function.update z.2 e g) * D z.2 e g ∂μ) /
      (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num) beta hbeta z *
       normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num) beta hbeta z.2) := by
  classical
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) beta hbeta f
  let q := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num) beta hbeta z *
    normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num) beta hbeta z.2
  have hD := p4Q2GN_originalDensityContrast_continuous H beta hbeta z.2 e
  have hiD : Integrable (D z.2 e) μ :=
    hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUp : Continuous (fun g : Gauge => (z.1, Function.update z.2 e g)) := by fun_prop
  have hiO : Integrable (fun g => O (z.1, Function.update z.2 e g) * D z.2 e g) μ :=
    ((O.continuous.comp hUp).mul hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing]
  calc
    (∫ g : Gauge, p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e (z,g) * D z.2 e g ∂μ) =
      ∫ g : Gauge, (O z * D z.2 e g -
        O (z.1, Function.update z.2 e g) * D z.2 e g) / q ∂μ := by
          apply integral_congr_ae
          filter_upwards with g
          rw [p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_apply]
          change ((O z - O (z.1, Function.update z.2 e g)) / q) * D z.2 e g = _
          ring
    _ = ((∫ g, O z * D z.2 e g ∂μ) -
        (∫ g, O (z.1, Function.update z.2 e g) * D z.2 e g ∂μ)) / q := by
          rw [integral_div, integral_sub (hiD.const_mul (O z)) hiO]
    _ = -(∫ g, O (z.1, Function.update z.2 e g) * D z.2 e g ∂μ) / q := by
          rw [integral_const_mul, p4Q2GN_originalDensityContrast_integral_zero H beta hbeta z.2 e]
          ring

/-- Exact original physical detector in terms of the original Wilson
kernel integral. Its prefactor is nonzero also at beta=0. -/
theorem p4Q2GN_originalExpectationGap_eq_transferFiberMoment
    (f : Phys) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H beta hbeta f e z =
    (-L * s z) * p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z := by
  classical
  have hL : L ≠ 0 := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta)).ne'
  have hs := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta z).ne'
  have hi : (∫ g : Gauge,
      normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) beta hbeta f
        (z.1, Function.update z.2 e g) * D z.2 e g ∂μ) =
      L ^ 2 * p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z := by
    unfold p4Q2GN_originalTransferFiberContrastMoment
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with g
    rw [p4Q2GN_originalReceiver_eq_transferIntegral]
    ring
  rw [p4Q2GN_originalExpectationGap_eq_updatedReceiverContrast, hi,
    p4Q2GN_originalDensityCancellationWeight_eq]
  field_simp [hL, hs]

/-- Pointwise kernel criterion without any assumption of detectability. -/
theorem p4Q2GN_originalExpectationGap_zero_iff_transferFiber_zero
    (f : Phys) (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H beta hbeta f e z = 0 ↔
    p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z = 0 := by
  have hL : L ≠ 0 := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta)).ne'
  have hs := (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta z).ne'
  have hc : (-L * s z) ≠ 0 := mul_ne_zero (by
    intro h
    apply hL
    linarith) hs
  rw [p4Q2GN_originalExpectationGap_eq_transferFiberMoment]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    rw [h, mul_zero]

/-- The outer pair-Haar detector kernel is exactly the explicit
Wilson-transfer fiber kernel, with no new measure or source certificate. -/
theorem p4Q2GN_originalExpectationGap_ae_zero_iff_transferFiber_ae_zero
    (f : Phys) (e : Link) :
    (∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H beta hbeta f e z = 0) ↔
    (∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z = 0) := by
  constructor
  · intro h
    filter_upwards [h] with z hz
    exact (p4Q2GN_originalExpectationGap_zero_iff_transferFiber_zero H beta hbeta f e z).mp hz
  · intro h
    filter_upwards [h] with z hz
    exact (p4Q2GN_originalExpectationGap_zero_iff_transferFiber_zero H beta hbeta f e z).mpr hz

/-- GB--GI's genuine source-link mass kernel is characterized by an
integral of the original Wilson kernel and source. -/
theorem p4Q2GN_originalSourceLinkMass_zero_iff_transferFiber_ae_zero
    (hpos : 0 < beta) (f : Phys) (e : Link) :
    p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean H beta hbeta f e = 0 ↔
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z = 0 := by
  exact (p4Q2GI_originalWilsonSourceLinkMass_zero_iff_expectationGap_ae_zero H beta hpos f e).trans
    (p4Q2GN_originalExpectationGap_ae_zero_iff_transferFiber_ae_zero H beta hbeta f e)

/-- GM's exact GL gap-square link mass has precisely the same explicit
original-transfer fiber kernel. This imports and extends the preceding GM. -/
theorem p4Q2GN_originalGapSquareLinkMass_zero_iff_transferFiber_ae_zero
    (hpos : 0 < beta) (f : Phys) (e : Link) :
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean H beta hbeta f e = 0 ↔
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z = 0 := by
  exact (p4Q2GM_originalWilsonGapSquareLinkMean_zero_iff_gapAE H beta hpos f e).trans
    (p4Q2GN_originalExpectationGap_ae_zero_iff_transferFiber_ae_zero H beta hbeta f e)

/-- Kernel containment is derived from the real Wilson transfer, not
from a postulated nondegenerate or independent-coordinate source model. -/
theorem p4Q2GN_originalTransferNull_implies_detectorNull
    (f : Phys)
    (hf : ∀ B : Cfg, decomposableOneSliceTransferIntegral H 2 beta f B = 0)
    (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H beta hbeta f e z = 0 := by
  rw [p4Q2GN_originalExpectationGap_eq_transferFiberMoment]
  have hJ : p4Q2GN_originalTransferFiberContrastMoment H beta hbeta f e z = 0 := by
    unfold p4Q2GN_originalTransferFiberContrastMoment
    simp only [hf, zero_div, zero_mul, integral_zero]
  rw [hJ, mul_zero]

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Actual fine-right Krylov coefficient kernel using the frozen
Wilson transfer. No generic replacement source family is introduced. -/
theorem p4Q2GN_actualFineRightKrylov_linkKernel_iff
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e = 0 ↔
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
      p4Q2GN_originalTransferFiberContrastMoment Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
  exact p4Q2GN_originalGapSquareLinkMass_zero_iff_transferFiber_ae_zero
    Hn (beta n) (hbeta n) hFrozen _ e

/-- Exact criterion for the original fine-evolved left three
Gram--Schmidt factors, still using the frozen posterior at beta(n). -/
theorem p4Q2GN_actualFineLeftThreeMode_linkKernel_iff
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean Hn (beta n) (hbeta n)
      (∑ k : Fin 3, a k • LeftFactor n r k) e = 0 ↔
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
      p4Q2GN_originalTransferFiberContrastMoment Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k) e z = 0 := by
  exact p4Q2GN_originalGapSquareLinkMass_zero_iff_transferFiber_ae_zero
    Hn (beta n) (hbeta n) hFrozen _ e

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalDensityContrast_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalDensityContrast_integral_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalDensityCancellationWeight_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalReceiver_eq_transferIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalSignedResponse_eq_transferDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalTransferFiberContrast_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalExpectationGap_eq_updatedReceiverContrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalExpectationGap_eq_transferFiberMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalExpectationGap_zero_iff_transferFiber_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalExpectationGap_ae_zero_iff_transferFiber_ae_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalSourceLinkMass_zero_iff_transferFiber_ae_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalGapSquareLinkMass_zero_iff_transferFiber_ae_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_originalTransferNull_implies_detectorNull
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_actualFineRightKrylov_linkKernel_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GN_actualFineLeftThreeMode_linkKernel_iff
