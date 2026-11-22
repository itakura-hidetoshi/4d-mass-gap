import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalConditionalHaarRemainderV5_PZ37AOI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOM — original fixed-left Wilson row linear-response remainder

This module contains a research candidate for the ORIGINAL finite-volume SU(2)
Wilson one-slab kernel and the ORIGINAL normalized spatial-slice Haar.

AOG's certified center-twist Haar antisymmetrization is made public for
arbitrary continuous row functions, and combined with AOI's already certified
conditional Haar Taylor residual bound. For beta >= 0 with 8*beta <= 1,
the ORIGINAL unnormalized fixed-left primary-character row response differs
from its beta-weighted local flipped-action coefficient by <= 64*beta²,
uniformly in finite H and fixed left boundary A.

The weighted local coefficient is NOT replaced by its zero-coupling Haar value.
No uniform physical top-eigenvector slope, normalized amplitude, spectral
gap, infinite-volume limit, or 4D Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOM_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOM_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOM_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOM_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOM_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOM_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37AOM_singleLinkCenterTwist_continuous
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (p4Q2PZ37ANV_singleLinkCenterTwist H target) := by
  classical
  unfold p4Q2PZ37ANV_singleLinkCenterTwist
  apply continuous_pi
  intro e
  exact (continuous_apply e).mul continuous_const

private theorem p4Q2PZ37AOM_primaryCharacter_centerTwist_odd
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (p4Q2PZ37ANV_singleLinkCenterTwist H
        (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)) =
      -Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) := by
  rw [p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU]
  exact p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd
    H (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) (Or.inl rfl) B

private theorem p4Q2PZ37AOM_primaryCharacter_continuous (H : ℕ) :
    Continuous
      (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) := by
  have heq :
      (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) =
      (fun B => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
    funext B
    exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
  rw [heq]
  exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
    H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)

/-- Public, exact version of the already AOG-verified original Haar
antisymmetrization: the twist moves *one genuine original spatial link*.
No modified measure or synthetic independent plaquette is introduced. -/
theorem p4Q2PZ37AOM_originalHaarPrimaryCharacter_antisymmetrization
    (H : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ)
    (hF : Continuous F) :
    (-2 : ℝ) *
      (∫ B, F B * Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      -(∫ B, (F B - F (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  have hChi : Continuous chi := p4Q2PZ37AOM_primaryCharacter_continuous H
  have hTau : Continuous tau := p4Q2PZ37AOM_singleLinkCenterTwist_continuous H _
  have hMP : MeasurePreserving tau mu mu :=
    p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving H _
  have hOdd (B : Cfg) : chi (tau B) = -chi B :=
    p4Q2PZ37AOM_primaryCharacter_centerTwist_odd H B
  have hTransport :
      (∫ B, F (tau B) * chi (tau B) ∂mu) = ∫ B, F B * chi B ∂mu := by
    have hMap :
        (∫ B, F B * chi B ∂Measure.map tau mu) =
          ∫ B, F (tau B) * chi (tau B) ∂mu :=
      integral_map hMP.measurable.aemeasurable
        (hF.mul hChi).measurable.aestronglyMeasurable
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hTwisted : (∫ B, F (tau B) * chi B ∂mu) =
      -(∫ B, F B * chi B ∂mu) := by
    have hNeg : (∫ B, F (tau B) * chi (tau B) ∂mu) =
        -(∫ B, F (tau B) * chi B ∂mu) := by
      simp_rw [hOdd, mul_neg]
      rw [integral_neg]
    rw [hNeg] at hTransport
    linarith only [hTransport]
  have hInt : Integrable (fun B => F B * chi B) mu :=
    (hF.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTwistedInt : Integrable (fun B => F (tau B) * chi B) mu :=
    ((hF.comp hTau).mul hChi).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDifference :
      (∫ B, (F B - F (tau B)) * chi B ∂mu) =
        (∫ B, F B * chi B ∂mu) - (∫ B, F (tau B) * chi B ∂mu) := by
    calc
      _ = ∫ B, F B * chi B - F (tau B) * chi B ∂mu := by
        apply integral_congr_ae
        filter_upwards with B
        ring
      _ = _ := integral_sub hInt hTwistedInt
  change (-2 : ℝ) * (∫ B, F B * chi B ∂mu) =
    -(∫ B, (F B - F (tau B)) * chi B ∂mu)
  rw [hDifference, hTwisted]
  ring

/-- Fixed-left, actual original-kernel unnormalized first-character response
has an H-independent *quadratic absolute error* relative to the
beta-weighted, still-interacting, local flipped-action coefficient.
This is NOT a beta-uniform approximation of that coefficient by -1/4. -/
theorem p4Q2PZ37AOM_originalFixedLeftRowLocalLinearResponse_abs_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |(-2 : ℝ) *
        (∫ B,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 beta A B *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) -
      beta *
        (∫ B,
          p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 beta A
              (p4Q2PZ37ANV_singleLinkCenterTwist H
                (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| ≤
        64 * beta^2 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  let kernel : Cfg → ℝ := fun B =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  let delta : Cfg → ℝ := fun B =>
    p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B
  let residual : Cfg → ℝ := fun B =>
    p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B
  have hKernelCont : Continuous kernel :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp (continuous_const.prodMk continuous_id)
  have hTauCont : Continuous tau :=
    p4Q2PZ37AOM_singleLinkCenterTwist_continuous H _
  have hChiCont : Continuous chi :=
    p4Q2PZ37AOM_primaryCharacter_continuous H
  have hKtwistCont : Continuous (fun B : Cfg => kernel (tau B)) :=
    hKernelCont.comp hTauCont
  have hCrossCont : Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H 2).comp
      (continuous_const.prodMk continuous_id)
  have hWilsonCont :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hActionCont : Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B) := by
    dsimp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction]
    exact (continuous_const.add hCrossCont).add
      (continuous_const.mul hWilsonCont)
  have hDeltaCont : Continuous delta := by
    change Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A (tau B))
    exact hActionCont.sub (hActionCont.comp hTauCont)
  have hSubInt : Integrable (fun B : Cfg =>
      (kernel B - kernel (tau B)) * chi B) mu :=
    ((hKernelCont.sub hKtwistCont).mul hChiCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLinInt : Integrable (fun B : Cfg =>
      (beta * delta B * kernel (tau B)) * chi B) mu :=
    (((continuous_const.mul hDeltaCont).mul hKtwistCont).mul hChiCont)
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAnti :
      (-2 : ℝ) * (∫ B, kernel B * chi B ∂mu) =
      -(∫ B, (kernel B - kernel (tau B)) * chi B ∂mu) :=
    p4Q2PZ37AOM_originalHaarPrimaryCharacter_antisymmetrization
      H kernel hKernelCont
  have hBeta :
      beta * (∫ B, delta B * kernel (tau B) * chi B ∂mu) =
        ∫ B, (beta * delta B * kernel (tau B)) * chi B ∂mu := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with B
    ring
  have hResIntegral :
      (∫ B, residual B * chi B ∂mu) =
        (∫ B, (kernel B - kernel (tau B)) * chi B ∂mu) +
          (∫ B, (beta * delta B * kernel (tau B)) * chi B ∂mu) := by
    rw [← integral_add hSubInt hLinInt]
    apply integral_congr_ae
    filter_upwards [] with B
    dsimp [residual, kernel, delta, tau]
    ring
  have hBridge :
      (-2 : ℝ) * (∫ B, kernel B * chi B ∂mu) -
        beta * (∫ B, delta B * kernel (tau B) * chi B ∂mu) =
        -(∫ B, residual B * chi B ∂mu) := by
    rw [hAnti, hBeta, hResIntegral]
    ring
  have hBound :
      |∫ B, residual B * chi B ∂mu| ≤ 64 * beta^2 :=
    p4Q2PZ37AOI_originalConditionalHaarRightTwistTaylorRemainder_abs_le
      H beta hbeta hsmall A
  change |(-2 : ℝ) * (∫ B, kernel B * chi B ∂mu) -
    beta * (∫ B, delta B * kernel (tau B) * chi B ∂mu)| ≤ 64 * beta^2
  rw [hBridge]
  simpa only [abs_neg] using hBound

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOM_originalHaarPrimaryCharacter_antisymmetrization
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOM_originalFixedLeftRowLocalLinearResponse_abs_le
