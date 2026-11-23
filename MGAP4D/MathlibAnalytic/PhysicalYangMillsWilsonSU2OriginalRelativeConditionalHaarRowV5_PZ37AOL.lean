import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalConditionalHaarRemainderV5_PZ37AOI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOL — original conditional Haar Taylor residual relative to row mass

Keep the ORIGINAL finite-volume SU(2) Wilson action and original full native
spatial-slice product Haar measure, with the LEFT spatial boundary A fixed.

AOI certifies an absolute 64*beta^2 bound.  This candidate retains the true
Boltzmann row integral on the right side, using AOH's pointwise relative
quadratic bound and ANV's original Haar-preserving one-link center twist.

The theorem is NOT a first-action Haar moment, beta-weighted linear row
coefficient, normalized physical-top derivative, or Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOL_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOL_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOL_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOL_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOL_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _


private theorem p4Q2PZ37AOL_fixedLeftKernel_continuous
    (H : ℕ) (beta : ℝ) (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hPair : Continuous (fun B : Cfg => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg => B))
  change Continuous
    ((fun p : Cfg × Cfg => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta p.1 p.2) ∘
      (fun B : Cfg => (A, B)))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta).comp hPair

private theorem p4Q2PZ37AOL_fixedLeftCrossing_continuous
    (H : ℕ) (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hPair : Continuous (fun B : Cfg => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg => B))
  change Continuous
    ((fun p : Cfg × Cfg => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 p.1 p.2) ∘
      (fun B : Cfg => (A, B)))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H 2).comp hPair

private theorem p4Q2PZ37AOL_fixedLeftAction_continuous
    (H : ℕ) (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B) := by
  have hCross : Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B) :=
    p4Q2PZ37AOL_fixedLeftCrossing_continuous H A
  have hWilson := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  dsimp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction]
  exact (continuous_const.add hCross).add (continuous_const.mul hWilson)

/-- Stronger than AOI's absolute bound: the H-independent quadratic
Taylor error is controlled *relative to the actual Wilson row mass*.
The true Haar probability space and the full Wilson kernel are unchanged. -/
theorem p4Q2PZ37AOL_originalConditionalHaarRelativeTaylorResidual_abs_le_rowMass
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |∫ B,
      p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)| ≤
        64 * beta^2 *
          (∫ B,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H 2 beta A B
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  let kernel : Cfg → ℝ := fun B =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  let kFlip : Cfg → ℝ := fun B => kernel (tau B)
  let residual : Cfg → ℝ := fun B =>
    p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B
  let C : ℝ := 64 * beta^2
  haveI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hTauCont : Continuous tau := by
    dsimp only [tau]
    unfold p4Q2PZ37ANV_singleLinkCenterTwist
    apply continuous_pi
    intro e
    exact (continuous_apply e).mul continuous_const
  have hKernelCont : Continuous kernel :=
    p4Q2PZ37AOL_fixedLeftKernel_continuous H beta A
  have hKFlipCont : Continuous kFlip := hKernelCont.comp hTauCont
  have hChiCont : Continuous chi := by
    have hfun :
      chi = (fun B : Cfg =>
        GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
      funext B
      exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
    rw [hfun]
    exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
      H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)
  have hCrossCont : Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B) :=
    p4Q2PZ37AOL_fixedLeftCrossing_continuous H A
  have hWilsonCont :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hActionCont : Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B) :=
    p4Q2PZ37AOL_fixedLeftAction_continuous H A
  have hActionFlipCont : Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A (tau B)) :=
    hActionCont.comp hTauCont
  have hDeltaCont : Continuous (fun B : Cfg =>
      p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B) := by
    change Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A (tau B))
    exact hActionCont.sub hActionFlipCont
  have hResCont : Continuous residual := by
    change Continuous (fun B : Cfg =>
      kernel B - kFlip B +
        beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B * kFlip B)
    exact (hKernelCont.sub hKFlipCont).add
      ((continuous_const.mul hDeltaCont).mul hKFlipCont)
  have hFInt : Integrable (fun B : Cfg => residual B * chi B) mu :=
    (hResCont.mul hChiCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hKFlipInt : Integrable kFlip mu :=
    hKFlipCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hBound (B : Cfg) : ‖residual B * chi B‖ ≤ C * kFlip B := by
    have hResidual : |residual B| ≤ C * kFlip B := by
      change |p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B| ≤
        64 * beta^2 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A (tau B)
      change |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) +
        beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
            (p4Q2PZ37ANV_singleLinkCenterTwist H
              (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)| ≤ _
      exact p4Q2PZ37AOH_originalKernel_rightCenterTwist_relativeRemainder_abs_le
        H beta hbeta hsmall A B
    have hKNonneg : 0 ≤ kFlip B := by
      dsimp [kFlip, kernel]
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
      exact Real.exp_nonneg _
    have hChi : |chi B| ≤ 1 := by
      dsimp [chi]
      rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter]
      unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
      have hlow := specialUnitaryWilsonPlaquetteEnergy_nonneg
        (by norm_num : 0 < (2 : ℕ))
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
      have hup := specialUnitaryWilsonPlaquetteEnergy_le_two
        (by norm_num : 0 < (2 : ℕ))
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
      rw [abs_le]
      constructor <;> linarith only [hlow, hup]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |residual B| * |chi B| ≤ (C * kFlip B) * |chi B| :=
        mul_le_mul_of_nonneg_right hResidual (abs_nonneg _)
      _ ≤ (C * kFlip B) * 1 :=
        mul_le_mul_of_nonneg_left hChi (mul_nonneg (by positivity) hKNonneg)
      _ = C * kFlip B := by ring
  have hHaar : MeasurePreserving tau mu mu := by
    dsimp [tau, mu]
    exact p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving H
      (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  have hRow : (∫ B, kFlip B ∂mu) = ∫ B, kernel B ∂mu := by
    change (∫ B, kernel (tau B) ∂mu) = ∫ B, kernel B ∂mu
    have hMapped :
        (∫ B, kernel B ∂Measure.map tau mu) =
          ∫ B, kernel (tau B) ∂mu :=
      integral_map hHaar.measurable.aemeasurable
        hKernelCont.measurable.aestronglyMeasurable
    rw [hHaar.map_eq] at hMapped
    exact hMapped.symm
  change |∫ B, residual B * chi B ∂mu| ≤ C * ∫ B, kernel B ∂mu
  have hNorm :
      ‖∫ B, residual B * chi B ∂mu‖ ≤ C * ∫ B, kernel B ∂mu := by
    calc
      ‖∫ B, residual B * chi B ∂mu‖ ≤
          ∫ B, ‖residual B * chi B‖ ∂mu :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ B, C * kFlip B ∂mu := by
        apply integral_mono_ae hFInt.norm (hKFlipInt.const_mul C)
        filter_upwards [] with B
        exact hBound B
      _ = C * ∫ B, kFlip B ∂mu := integral_const_mul _ _
      _ = C * ∫ B, kernel B ∂mu := by rw [hRow]
  simpa only [Real.norm_eq_abs] using hNorm

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOL_originalConditionalHaarRelativeTaylorResidual_abs_le_rowMass
