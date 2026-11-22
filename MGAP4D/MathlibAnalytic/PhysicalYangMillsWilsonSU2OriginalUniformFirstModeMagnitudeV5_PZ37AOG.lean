import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLinearBudgetDiagonalLimitV5_PZ37AOF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOG — uniform magnitude of the original first-mode overlap

The canonical continuous representative of the actual normalized physical
vacuum has one-link Harnack ratio exp(8*beta), independently of the volume.
The genuine primary SU(2) character is odd under the Haar-preserving center
flip. Pairing these facts gives |<Omega,v1>| <= (exp(8*beta)-1)*a, where a is
the Haar integral of that same continuous representative and 0 <= a <= 1.
Thus the original overlap tends to zero along every moving-volume family
with beta tending to zero. No global action-budget smallness is required.

The Haar integral here is the amplitude integral of the L2 unit vacuum,
not a squared-density expectation. These estimates do not establish a
volume-uniform -1/4 slope, a sign, an infinite-volume vacuum, a spectral gap,
OS identification, or a continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOG_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOG_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOG_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOG_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOG_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37AOG_singleLinkCenterTwist_continuous
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (p4Q2PZ37ANV_singleLinkCenterTwist H target) := by
  classical
  unfold p4Q2PZ37ANV_singleLinkCenterTwist
  apply continuous_pi
  intro e
  exact (continuous_apply e).mul continuous_const

private theorem p4Q2PZ37AOG_primaryCharacter_centerTwist_odd
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (p4Q2PZ37ANV_singleLinkCenterTwist H
        (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) A)) =
      -Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) := by
  rw [p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU]
  exact p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd
    H (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) (Or.inl rfl) A

private theorem p4Q2PZ37AOG_primaryCharacter_abs_le_one
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

private theorem p4Q2PZ37AOG_primaryCharacter_continuous (H : ℕ) :
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

private theorem p4Q2PZ37AOG_singleLinkCenterTwist_eq_replaceLink
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2PZ37ANV_singleLinkCenterTwist H target B =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H 2 B target (B target * specialUnitaryTwoNegativeIdentity) := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self]
    simp [p4Q2PZ37ANV_singleLinkCenterTwist]
  · rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B target e (B target * specialUnitaryTwoNegativeIdentity) he]
    simp [p4Q2PZ37ANV_singleLinkCenterTwist, he]

/-- Replacing a link with its own genuine value leaves the configuration fixed. -/
private theorem p4Q2PZ37AOG_replaceLink_originalValue
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H 2 B target (B target) = B := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self
      H 2 B target (B target)
  · exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B target e (B target) he

private theorem p4Q2PZ37AOG_originalFirstCharacter_sliceHaar_antisymmetrization
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
  have hChi : Continuous chi := p4Q2PZ37AOG_primaryCharacter_continuous H
  have hTau : Continuous tau := p4Q2PZ37AOG_singleLinkCenterTwist_continuous H _
  have hMP : MeasurePreserving tau mu mu :=
    p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving H _
  have hOdd (A : Cfg) : chi (tau A) = -chi A :=
    p4Q2PZ37AOG_primaryCharacter_centerTwist_odd H A
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

private theorem p4Q2PZ37AOG_real_relativeDifference_abs_le
    (x y R : ℝ) (hx : 0 ≤ x) (hR : 1 ≤ R)
    (hxy : x ≤ R * y) (hyx : y ≤ R * x) :
    |x - y| ≤ (R - 1) * x := by
  apply abs_le.mpr
  constructor
  · linarith only [hyx]
  · by_cases hy : y ≤ x
    · have hmul := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hR)
      nlinarith only [hxy, hmul]
    · have hnonneg := mul_nonneg (sub_nonneg.mpr hR) hx
      linarith only [lt_of_not_ge hy, hnonneg]

private theorem p4Q2PZ37AOG_originalContinuousVacuum_centerTwistDifference_ae_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2),
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta A -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) A)| ≤
        (Real.exp (8 * beta) - 1) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H 2 (by norm_num) beta hbeta A := by
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta
  let target := p4Q2PZ37AMS_primarySpatialSliceEdge H 0
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H target
  have hR : 1 ≤ Real.exp (8 * beta) := Real.one_le_exp (by positivity)
  have hForward (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
      F (tau A) ≤ Real.exp (8 * beta) * F A := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H 2 (by norm_num) beta hbeta A target
        (A target * specialUnitaryTwoNegativeIdentity) (A target)
    rw [← p4Q2PZ37AOG_singleLinkCenterTwist_eq_replaceLink H target A,
      p4Q2PZ37AOG_replaceLink_originalValue H target A] at h
    exact h
  have hReverse (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
      F A ≤ Real.exp (8 * beta) * F (tau A) := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H 2 (by norm_num) beta hbeta A target
        (A target) (A target * specialUnitaryTwoNegativeIdentity)
    rw [← p4Q2PZ37AOG_singleLinkCenterTwist_eq_replaceLink H target A,
      p4Q2PZ37AOG_replaceLink_originalValue H target A] at h
    exact h
  have hRep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) beta hbeta
  have hNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta
  filter_upwards [hRep, hNonneg] with A hA hPos
  have hFA : 0 ≤ F A := by
    dsimp [F]
    rw [hA]
    exact hPos
  exact p4Q2PZ37AOG_real_relativeDifference_abs_le
    (F A) (F (tau A)) (Real.exp (8 * beta)) hFA hR (hReverse A) (hForward A)

/-- The amplitude integral of the actual continuous physical unit vacuum
lies in [0,1]. It is the Haar constant-mode coefficient, not a density mean. -/
theorem p4Q2PZ37AOG_originalContinuousVacuum_haarIntegral_bounds
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) ∧
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) ≤ 1 := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hRep : F =ᵐ[mu] (fun A => (Ω : Lp ℝ 2 mu) A) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) beta hbeta
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hMass : (∫ A, F A ∂mu) = inner ℝ c Ω := by
    calc
      _ = ∫ A, (Ω : Lp ℝ 2 mu) A ∂mu := integral_congr_ae hRep
      _ = inner ℝ c Ω := by
        change (∫ A, (Ω : Lp ℝ 2 mu) A ∂mu) =
          inner ℝ (Lp.const 2 mu (1 : ℝ)) (Ω : Lp ℝ 2 mu)
        exact (realL2_inner_const_one_eq_integral (Ω : Lp ℝ 2 mu)).symm
  have hNonneg : ∀ᵐ A ∂mu, 0 ≤ F A := by
    have hOmega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H 2 (by norm_num) beta hbeta
    filter_upwards [hRep, hOmega] with A hA hPos
    rw [hA]
    exact hPos
  change 0 ≤ (∫ A, F A ∂mu) ∧ (∫ A, F A ∂mu) ≤ 1
  constructor
  · exact integral_nonneg_of_ae hNonneg
  · rw [hMass]
    calc
      inner ℝ c Ω ≤ |inner ℝ c Ω| := le_abs_self _
      _ ≤ ‖c‖ * ‖Ω‖ := abs_real_inner_le_norm c Ω
      _ = 1 := by
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
            H 2 (by norm_num) beta hbeta]
        norm_num

/-- Local center-flip cancellation controls the actual first overlap by
the same vacuum's amplitude integral, uniformly in every finite volume. -/
theorem p4Q2PZ37AOG_originalPhysicalTopFirst_abs_le_exp_sub_one_mul_haarIntegral
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      (Real.exp (8 * beta) - 1) *
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H 2 (by norm_num) beta hbeta A
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let v := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun A =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
  let q : ℝ := Real.exp (8 * beta) - 1
  have hF : Continuous F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hbeta
  have hChi : Continuous chi := p4Q2PZ37AOG_primaryCharacter_continuous H
  have hTau : Continuous tau := p4Q2PZ37AOG_singleLinkCenterTwist_continuous H _
  have hRep : F =ᵐ[mu] (fun A => (Ω : Lp ℝ 2 mu) A) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) beta hbeta
  have hMode : (v : Lp ℝ 2 mu) =ᵐ[mu] (fun A => (-2 : ℝ) * chi A) :=
    p4Q2PZ37ANV_actualPhysicalFirstGaussMode_haarRepresentative H
  have hScalar : inner ℝ Ω v = (-2 : ℝ) * (∫ A, F A * chi A ∂mu) := by
    change inner ℝ (Ω : Lp ℝ 2 mu) (v : Lp ℝ 2 mu) = _
    rw [MeasureTheory.L2.inner_def]
    calc
      _ = ∫ A, (-2 : ℝ) * (F A * chi A) ∂mu := by
        apply integral_congr_ae
        filter_upwards [hRep, hMode] with A hA hV
        rw [periodicHypercubicEven_real_inner_eq_mul, ← hA, hV]
        ring
      _ = _ := integral_const_mul (-2 : ℝ) _
  have hAnti : (-2 : ℝ) * (∫ A, F A * chi A ∂mu) =
      -(∫ A, (F A - F (tau A)) * chi A ∂mu) :=
    p4Q2PZ37AOG_originalFirstCharacter_sliceHaar_antisymmetrization H F hF
  have hDiff : ∀ᵐ A ∂mu, |F A - F (tau A)| ≤ q * F A :=
    p4Q2PZ37AOG_originalContinuousVacuum_centerTwistDifference_ae_le H beta hbeta
  have hIntegrableAbs : Integrable
      (fun A => |(F A - F (tau A)) * chi A|) mu :=
    (((hF.sub (hF.comp hTau)).mul hChi).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegrableUpper : Integrable (fun A => q * F A) mu :=
    (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul q
  have hPoint : ∀ᵐ A ∂mu, |(F A - F (tau A)) * chi A| ≤ q * F A := by
    filter_upwards [hDiff] with A hA
    rw [abs_mul]
    calc
      _ ≤ |F A - F (tau A)| * 1 :=
        mul_le_mul_of_nonneg_left
          (p4Q2PZ37AOG_primaryCharacter_abs_le_one H A) (abs_nonneg _)
      _ = |F A - F (tau A)| := mul_one _
      _ ≤ q * F A := hA
  change |inner ℝ Ω v| ≤ q * (∫ A, F A ∂mu)
  rw [hScalar, hAnti, abs_neg]
  calc
    _ ≤ ∫ A, |(F A - F (tau A)) * chi A| ∂mu := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := mu) (fun A : Cfg => (F A - F (tau A)) * chi A))
    _ ≤ ∫ A, q * F A ∂mu :=
      integral_mono_ae hIntegrableAbs hIntegrableUpper hPoint
    _ = q * (∫ A, F A ∂mu) := integral_const_mul q _

/-- The actual normalized top/first overlap has a bound independent of H
at every nonnegative coupling, with no global-budget smallness premise. -/
theorem p4Q2PZ37AOG_originalPhysicalTopFirst_abs_le_exp_sub_one
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤ Real.exp (8 * beta) - 1 := by
  have hWeighted :=
    p4Q2PZ37AOG_originalPhysicalTopFirst_abs_le_exp_sub_one_mul_haarIntegral H beta hbeta
  have hMass := p4Q2PZ37AOG_originalContinuousVacuum_haarIntegral_bounds H beta hbeta
  have hq : 0 ≤ Real.exp (8 * beta) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  exact hWeighted.trans ((mul_le_mul_of_nonneg_left hMass.2 hq).trans_eq (mul_one _))

open scoped NNReal

/-- Vanishing coupling alone gives vanishing original overlap magnitude
along arbitrary moving finite volumes. No C_H*beta limit is assumed. -/
theorem p4Q2PZ37AOG_originalPhysicalTopFirst_abs_tendsto_zero
    {ι : Type*} (l : Filter ι) (H : ι → ℕ) (beta : ι → ℝ≥0)
    (hbeta : Tendsto (fun i => (beta i : ℝ)) l (𝓝 (0 : ℝ))) :
    Tendsto
      (fun i => |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property)
        (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)|)
      l (𝓝 (0 : ℝ)) := by
  have hScaled : Tendsto (fun i => 8 * (beta i : ℝ)) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hbeta.const_mul (8 : ℝ)
  have hExp : Tendsto (fun i => Real.exp (8 * (beta i : ℝ)) - 1)
      l (𝓝 (0 : ℝ)) := by
    simpa only [Real.exp_zero, sub_self] using
      ((Real.continuous_exp.tendsto (0 : ℝ)).comp hScaled).sub_const (1 : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hExp
    (Eventually.of_forall fun i => abs_nonneg _)
    (Eventually.of_forall fun i =>
      p4Q2PZ37AOG_originalPhysicalTopFirst_abs_le_exp_sub_one
        (H i) (beta i : ℝ) (beta i).property)

/-- The actual signed physical overlap also tends to zero for arbitrary
moving finite volumes whenever the nonnegative coupling tends to zero. -/
theorem p4Q2PZ37AOG_originalPhysicalTopFirst_tendsto_zero
    {ι : Type*} (l : Filter ι) (H : ι → ℕ) (beta : ι → ℝ≥0)
    (hbeta : Tendsto (fun i => (beta i : ℝ)) l (𝓝 (0 : ℝ))) :
    Tendsto
      (fun i => inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property)
        (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1))
      l (𝓝 (0 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, Real.norm_eq_abs] using
    p4Q2PZ37AOG_originalPhysicalTopFirst_abs_tendsto_zero l H beta hbeta

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOG_originalContinuousVacuum_haarIntegral_bounds
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOG_originalPhysicalTopFirst_abs_le_exp_sub_one_mul_haarIntegral
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOG_originalPhysicalTopFirst_abs_le_exp_sub_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOG_originalPhysicalTopFirst_abs_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOG_originalPhysicalTopFirst_tendsto_zero
