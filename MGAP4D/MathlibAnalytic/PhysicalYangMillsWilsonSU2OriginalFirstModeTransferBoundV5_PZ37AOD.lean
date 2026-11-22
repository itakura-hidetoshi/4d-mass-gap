import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLocalCenterFlipTaylorV5_PZ37AOC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneLinkChordKernelModulusV5_PZ37AEM
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2VacuumStabilityFixedSourceResponseV5_PZ37ANR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOD — original physical transfer on the first Gauss-law mode

The genuine first Wilson mode has the original Haar representative -2 times
the primary character.  Antisymmetrizing its actual transfer integral under
the Haar-preserving primary-link center twist combines the local action
oscillation of eight with the nonnegative-action Boltzmann Lipschitz bound.
This proves ||T_beta v_1|| <= 8 beta for every finite H and beta >= 0.

The actual physical transfer is symmetric.  Moving it to the observed mode
before Cauchy--Schwarz, and then using ANR's weighted true-vacuum displacement,
bounds the weighted vacuum-replacement error by 16 C_H beta^2.  Both estimates
use the unchanged physical operator, Haar measure, and normalized top state.
No volume-uniform full operator perturbation, vacuum displacement, spectral
gap, infinite-volume state, OS identification, or continuum mass gap follows.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOD_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOD_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOD_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOD_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOD_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOD_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37AOD_singleLinkCenterTwist_continuous
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (p4Q2PZ37ANV_singleLinkCenterTwist H target) := by
  classical
  unfold p4Q2PZ37ANV_singleLinkCenterTwist
  apply continuous_pi
  intro e
  exact (continuous_apply e).mul continuous_const

private theorem p4Q2PZ37AOD_primaryCharacter_centerTwist_odd
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (p4Q2PZ37ANV_singleLinkCenterTwist H
        (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) A)) =
      -Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) := by
  rw [p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU]
  exact p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd
    H (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) (Or.inl rfl) A

private theorem p4Q2PZ37AOD_primaryCharacter_abs_le_one
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)| ≤ 1 := by
  rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter]
  unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
  have hlow := specialUnitaryWilsonPlaquetteEnergy_nonneg
    (by norm_num : 0 < (2 : ℕ))
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  have hup := specialUnitaryWilsonPlaquetteEnergy_le_two
    (by norm_num : 0 < (2 : ℕ))
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  rw [abs_le]
  constructor <;> linarith

private theorem p4Q2PZ37AOD_primaryCharacter_continuous (H : ℕ) :
    Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
  have heq :
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) =
      (fun A => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) A) := by
    funext A
    exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H A
  rw [heq]
  exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
    H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)

/-- AOC's complete-action oscillation gives a volume-independent bound for
the actual Wilson kernel under every original single-link center twist. -/
theorem p4Q2PZ37AOD_originalKernel_rightCenterTwist_sub_abs_le_eightBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
        (p4Q2PZ37ANV_singleLinkCenterTwist H target B) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B| ≤
      8 * beta := by
  let B' := p4Q2PZ37ANV_singleLinkCenterTwist H target B
  let x := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B'
  let y := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B
  have hx : 0 ≤ x :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B'
  have hy : 0 ≤ y :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have hxy : |x - y| ≤ 8 :=
    p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight
      H target A B
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  change |Real.exp (-beta * x) - Real.exp (-beta * y)| ≤ 8 * beta
  calc
    _ ≤ beta * |x - y| :=
      p4Q2PZ37AEM_real_nonnegativeWilsonBoltzmannLipschitz beta x y hbeta hx hy
    _ ≤ beta * 8 := mul_le_mul_of_nonneg_left hxy hbeta
    _ = 8 * beta := mul_comm _ _

/-- Single-slice cancellation uses the actual Haar law and primary link. -/
private theorem p4Q2PZ37AOD_originalFirstCharacter_sliceHaar_antisymmetrization
    (H : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ)
    (hF : Continuous F) :
    (-2 : ℝ) *
      (∫ A, F A * Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      -(∫ A, (F A - F (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) A)) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun A =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
  have hChi : Continuous chi := p4Q2PZ37AOD_primaryCharacter_continuous H
  have hTau : Continuous tau := p4Q2PZ37AOD_singleLinkCenterTwist_continuous H _
  have hMP : MeasurePreserving tau mu mu :=
    p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving H _
  have hOdd (A : Cfg) : chi (tau A) = -chi A :=
    p4Q2PZ37AOD_primaryCharacter_centerTwist_odd H A
  have hTransport :
      (∫ A, F (tau A) * chi (tau A) ∂mu) = ∫ A, F A * chi A ∂mu := by
    have hMap :
        (∫ A, F A * chi A ∂Measure.map tau mu) =
          ∫ A, F (tau A) * chi (tau A) ∂mu :=
      integral_map hMP.measurable.aemeasurable
        (hF.mul hChi).measurable.aestronglyMeasurable
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hTwisted : (∫ A, F (tau A) * chi A ∂mu) =
      -(∫ A, F A * chi A ∂mu) := by
    have hNeg : (∫ A, F (tau A) * chi (tau A) ∂mu) =
        -(∫ A, F (tau A) * chi A ∂mu) := by
      simp_rw [hOdd, mul_neg]
      rw [integral_neg]
    rw [hNeg] at hTransport
    linarith only [hTransport]
  have hInt : Integrable (fun A => F A * chi A) mu :=
    (hF.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTwistedInt : Integrable (fun A => F (tau A) * chi A) mu :=
    ((hF.comp hTau).mul hChi).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDifference :
      (∫ A, (F A - F (tau A)) * chi A ∂mu) =
        (∫ A, F A * chi A ∂mu) - (∫ A, F (tau A) * chi A ∂mu) := by
    calc
      _ = ∫ A, F A * chi A - F (tau A) * chi A ∂mu := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ = _ := integral_sub hInt hTwistedInt
  change (-2 : ℝ) * (∫ A, F A * chi A ∂mu) =
    -(∫ A, (F A - F (tau A)) * chi A ∂mu)
  rw [hDifference, hTwisted]
  ring

/-- Preserve the actual first-mode representative through scalar congruence,
without rewriting inside the concrete physical-to-Lp coercion. -/
private theorem p4Q2PZ37AOD_originalFirstMode_transferIntegralRepresentative_eq_characterIntegral
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H 2 beta
        ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) B =
      (-2 : ℝ) * (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta B A *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let v1 : Lp ℝ 2 mu :=
    ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) : Lp ℝ 2 mu)
  have hMode : v1 =ᵐ[mu] (fun A => (-2 : ℝ) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) :=
    p4Q2PZ37ANV_actualPhysicalFirstGaussMode_haarRepresentative H
  change (∫ A : Cfg, v1 A *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B ∂mu) = _
  calc
    _ = ∫ A : Cfg, (-2 : ℝ) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta B A *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hMode] with A hA
      calc
        _ = ((-2 : ℝ) *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta B A :=
          congrArg₂ (fun a b : ℝ => a * b) hA
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
              H 2 (by norm_num) beta hbeta A B)
        _ = _ := by ring
    _ = _ := integral_const_mul (-2 : ℝ) _

/-- Prove the probability estimate for an arbitrary continuous function
before any concrete Wilson kernel is substituted into the proof. -/
private theorem p4Q2PZ37AOD_originalFirstCharacter_sliceHaar_abs_le_of_centerTwist_bound
    (H : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ)
    (hF : Continuous F) (C : ℝ)
    (hOsc : ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      |F (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) A) - F A| ≤ C) :
    |(-2 : ℝ) * (∫ A,
        F A * Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| ≤ C := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun A =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hAntisym : (-2 : ℝ) * (∫ A, F A * chi A ∂mu) =
      -(∫ A, (F A - F (tau A)) * chi A ∂mu) :=
    p4Q2PZ37AOD_originalFirstCharacter_sliceHaar_antisymmetrization H F hF
  have hPoint (A : Cfg) : ‖(F A - F (tau A)) * chi A‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |F A - F (tau A)| * 1 :=
        mul_le_mul_of_nonneg_left
          (p4Q2PZ37AOD_primaryCharacter_abs_le_one H A) (abs_nonneg _)
      _ = |F A - F (tau A)| := mul_one _
      _ ≤ C := (abs_sub_comm (F A) (F (tau A))).le.trans (hOsc A)
  have hIntegral : |∫ A, (F A - F (tau A)) * chi A ∂mu| ≤ C := by
    have h := norm_integral_le_of_norm_le_const (μ := mu)
      (f := fun A : Cfg => (F A - F (tau A)) * chi A)
      (C := C) (Eventually.of_forall hPoint)
    simpa [Real.norm_eq_abs] using h
  calc
    _ = |-(∫ A, (F A - F (tau A)) * chi A ∂mu)| := congrArg abs hAntisym
    _ = |∫ A, (F A - F (tau A)) * chi A ∂mu| := abs_neg _
    _ ≤ C := hIntegral

/-- Joint continuity of the unchanged kernel restricts to a fixed left
boundary; this small application is checked separately from integration. -/
private theorem p4Q2PZ37AOD_originalKernel_fixedLeft_continuous
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta B A) := by
  have hPair : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        (B, A)) := continuous_const.prodMk continuous_id
  have hComp :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp hPair
  exact hComp

/-- Specialize the abstract scalar estimate to the original kernel using
its already-proved local center-twist bound. -/
private theorem p4Q2PZ37AOD_originalKernel_firstCharacterIntegral_abs_le_eightBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |(-2 : ℝ) * (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta B A *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| ≤
      8 * beta := by
  exact p4Q2PZ37AOD_originalFirstCharacter_sliceHaar_abs_le_of_centerTwist_bound H
    (fun A => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta B A)
    (p4Q2PZ37AOD_originalKernel_fixedLeft_continuous H beta B)
    (8 * beta)
    (fun A => p4Q2PZ37AOD_originalKernel_rightCenterTwist_sub_abs_le_eightBeta
      H beta hbeta (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B A)

/-- The original transfer's actual integral representative on its genuine
first physical Gauss-law mode is bounded at every right boundary. -/
theorem p4Q2PZ37AOD_originalFirstMode_transferIntegralRepresentative_abs_le_eightBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H 2 beta
        ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) B| ≤
      8 * beta := by
  exact (congrArg abs
    (p4Q2PZ37AOD_originalFirstMode_transferIntegralRepresentative_eq_characterIntegral
      H beta hbeta B)).le.trans
    (p4Q2PZ37AOD_originalKernel_firstCharacterIntegral_abs_le_eightBeta H beta hbeta B)

/-- The actual physical first-mode image has a volume-independent norm
bound.  The original ambient integral and physical restriction are linked
by their existing coercion theorems; no new transfer model is defined. -/
theorem p4Q2PZ37AOD_originalPhysicalFirstMode_transfer_norm_le_eightBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)‖ ≤
      8 * beta := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let v1 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let f : Lp ℝ 2 mu :=
    ((T v1 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
      Lp ℝ 2 mu)
  let g : Lp ℝ 2 mu := Lp.const 2 mu (8 * beta)
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hRep : f =ᵐ[mu]
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H 2 beta (v1 : Lp ℝ 2 mu) := by
    change
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta v1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
        Lp ℝ 2 mu) =ᵐ[mu] _
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
      H 2 (by norm_num) beta hbeta (v1 : Lp ℝ 2 mu)
  have hConst := Lp.coeFn_const (μ := mu) (p := (2 : ENNReal)) (c := 8 * beta)
  have hNonneg : 0 ≤ 8 * beta := mul_nonneg (by norm_num) hbeta
  have hle : ∀ᵐ B ∂mu, ‖f B‖ ≤ ‖g B‖ := by
    filter_upwards [hRep, hConst] with B hB hC
    change ‖f B‖ ≤ ‖(Lp.const 2 mu (8 * beta)) B‖
    rw [hB, hC]
    simpa only [Function.const_apply, Real.norm_eq_abs, abs_of_nonneg hNonneg] using
      (p4Q2PZ37AOD_originalFirstMode_transferIntegralRepresentative_abs_le_eightBeta
        H beta hbeta B)
  have hNorm : ‖f‖ ≤ ‖g‖ := Lp.norm_le_norm_of_ae_le hle
  have hNormConst : ‖g‖ = 8 * beta := by
    have h := Lp.norm_const' (μ := mu) (p := (2 : ENNReal))
      (c := 8 * beta) (by norm_num) (by norm_num)
    simpa [g, Real.norm_eq_abs, abs_of_nonneg hbeta] using h
  change ‖f‖ ≤ 8 * beta
  exact hNorm.trans_eq hNormConst

/-- Symmetry places the actual transfer on the observed first mode before
Cauchy--Schwarz in the exact true-vacuum replacement identity. -/
theorem p4Q2PZ37AOD_originalTopFirstMode_fixedHaarResponse_error_le_projected
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) -
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num))
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖ *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have hEigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hZero : inner ℝ (U c) v1 = 0 :=
    p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero H c
  have hFixed : inner ℝ ((T - U) c) v1 = inner ℝ (T c) v1 := by
    calc
      _ = inner ℝ (T c - U c) v1 := by rw [ContinuousLinearMap.sub_apply]
      _ = inner ℝ (T c) v1 - inner ℝ (U c) v1 :=
        inner_sub_left (𝕜 := ℝ) (T c) (U c) v1
      _ = inner ℝ (T c) v1 := by rw [hZero, sub_zero]
  have hTop : ‖T‖ * inner ℝ Ω v1 = inner ℝ (T Ω) v1 := by
    rw [hEigen]
    exact (real_inner_smul_left Ω v1 ‖T‖).symm
  have hIdentity :
      ‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1 =
        inner ℝ (Ω - c) (T v1) := by
    calc
      _ = inner ℝ (T Ω) v1 - inner ℝ (T c) v1 :=
        congrArg₂ (fun a b : ℝ => a - b) hTop hFixed
      _ = inner ℝ (T Ω - T c) v1 :=
        (inner_sub_left (𝕜 := ℝ) (T Ω) (T c) v1).symm
      _ = inner ℝ (T (Ω - c)) v1 := by rw [map_sub]
      _ = inner ℝ (Ω - c) (T v1) :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
          H 2 (by norm_num) beta hbeta (Ω - c) v1
  change |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| ≤
    ‖Ω - c‖ * ‖T v1‖
  rw [hIdentity]
  exact abs_real_inner_le_norm _ _

/-- The true-vacuum replacement error has a quadratic beta bound with
only one factor of the original global action budget, for every beta>=0. -/
theorem p4Q2PZ37AOD_originalTopFirstMode_fixedHaarResponse_weightedError_le_linearBudgetQuadratic
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H 2 (by norm_num) beta hbeta)
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) -
        inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) beta hbeta -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) 0 (by norm_num))
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      16 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta^2 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hCoef :
      |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| ≤ ‖Ω - c‖ * ‖T v1‖ :=
    p4Q2PZ37AOD_originalTopFirstMode_fixedHaarResponse_error_le_projected H beta hbeta
  have hMode : ‖T v1‖ ≤ 8 * beta :=
    p4Q2PZ37AOD_originalPhysicalFirstMode_transfer_norm_le_eightBeta H beta hbeta
  have hDistance : ‖T‖ * ‖Ω - c‖ ≤ 2 * (C * beta) :=
    p4Q2PZ37ANR_originalPhysicalVacuum_distance_weighted_le_twoBudgetBeta H beta hbeta
  have hNonneg : 0 ≤ 2 * (C * beta) :=
    mul_nonneg (by norm_num)
      (mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
        hbeta)
  change ‖T‖ * |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| ≤ 16 * C * beta^2
  calc
    _ ≤ ‖T‖ * (‖Ω - c‖ * ‖T v1‖) :=
      mul_le_mul_of_nonneg_left hCoef (norm_nonneg T)
    _ = (‖T‖ * ‖Ω - c‖) * ‖T v1‖ := by ring
    _ ≤ (2 * (C * beta)) * ‖T v1‖ :=
      mul_le_mul_of_nonneg_right hDistance (norm_nonneg (T v1))
    _ ≤ (2 * (C * beta)) * (8 * beta) :=
      mul_le_mul_of_nonneg_left hMode hNonneg
    _ = 16 * C * beta^2 := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOD_originalKernel_rightCenterTwist_sub_abs_le_eightBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOD_originalFirstMode_transferIntegralRepresentative_abs_le_eightBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOD_originalPhysicalFirstMode_transfer_norm_le_eightBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOD_originalTopFirstMode_fixedHaarResponse_error_le_projected
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOD_originalTopFirstMode_fixedHaarResponse_weightedError_le_linearBudgetQuadratic
