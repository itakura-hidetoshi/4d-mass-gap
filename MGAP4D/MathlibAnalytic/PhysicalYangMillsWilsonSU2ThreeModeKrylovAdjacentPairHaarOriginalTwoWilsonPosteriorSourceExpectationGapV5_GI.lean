import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalProjectedSourceAEKernelV5_GH
import Mathlib.Tactic

/-!
# P4-Q2-GI: actual physical signed Wilson receiver two-posterior expectation gap

Fix the genuine source-dependent FF relative signed original-Wilson BCF
receiver R_{beta,e,f}(z,g). GA's contrast compares two ACTUAL original
normalized Wilson posterior one-link conditional distributions at
distinct physical LEFT boundaries (identity versus physical pi-rotation)
and the SAME right physical background.

Define the genuine physical signed-response posterior-expectation gap:

 Delta_{beta,e,f}(z) =
     E_{nu_beta(left=identity,right=z.2,e)} [R(z,g)]
       - E_{nu_beta(left=pi,right=z.2,e)} [R(z,g)].

Both inner laws are the original interacting Wilson conditionals, not
independent Haar conditional substitutes.

Prove exactly that Delta equals the Haar pairing of R with the
genuine difference of the two normalized Wilson posterior densities
and, when beta>0, equals GA's nonzero Wilson density-row Haar squared
distance times GB's actual physical-source projection alpha.

Hence projected mass vanishes on a physical link exactly when
Delta vanishes pair-Haar-a.e. in its outer physical context.
One actual physical link with a not-a.e.-zero EXPECTATION GAP is
sufficient for positive original physical Gram Rayleigh.

No assumption or claim of existence of a nonzero source expectation gap,
source-frame coercivity, volume-uniform tail, H1-C3 closure or
continuum Yang–Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2GI_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Two ACTUAL interacting original-Wilson conditional expectations of the
same signed physical FF response under physically distinct left boundaries.
Their difference, not a surrogate Haar-conditional expectation, is the
physical source witness to be detected. -/
noncomputable def p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  let R := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta hbeta f e
  (∫ g, R (z,g) ∂
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) z.2 e)) -
  (∫ g, R (z,g) ∂
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) z.2 e))

/-- The source-response expectation gap under two ORIGINAL Wilson
conditional posterior measures is EXACTLY the reference Haar pairing
against their TRUE normalized density difference. Haar is only the
common integration reference for the two physical probability laws. -/
theorem p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e z =
    ∫ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e (z,g) *
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H beta hbeta z.2 e g
      ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta hbeta f e
  let X : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ := fun g => B (z,g)
  let L0 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) z.2 e
  let L1 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) z.2 e
  let P0 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    continuousNormalizedExp μ L0
  let P1 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    continuousNormalizedExp μ L1
  have hXcont : Continuous X :=
    B.continuous.comp (continuous_const.prodMk continuous_id)
  have hL0cont : Continuous L0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) z.2 e
  have hL1cont : Continuous L1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) z.2 e
  have hP0cont : Continuous P0 :=
    continuous_continuousNormalizedExp μ L0 hL0cont
  have hP1cont : Continuous P1 :=
    continuous_continuousNormalizedExp μ L1 hL1cont
  have hP0XInt : Integrable (fun g => P0 g * X g) μ :=
    (hP0cont.mul hXcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hP1XInt : Integrable (fun g => P1 g * X g) μ :=
    (hP1cont.mul hXcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h0 :
      (∫ g, X g ∂μ.tilted L0) =
        ∫ g, P0 g * X g ∂μ := by
    rw [integral_tilted]
    rfl
  have h1 :
      (∫ g, X g ∂μ.tilted L1) =
        ∫ g, P1 g * X g ∂μ := by
    rw [integral_tilted]
    rfl
  change (∫ g, X g ∂μ.tilted L0) -
      (∫ g, X g ∂μ.tilted L1) =
    ∫ g, X g * (P0 g - P1 g) ∂μ
  rw [h0, h1]
  calc
    (∫ g, P0 g * X g ∂μ) - (∫ g, P1 g * X g ∂μ) =
        ∫ g, (P0 g * X g - P1 g * X g) ∂μ :=
      (integral_sub hP0XInt hP1XInt).symm
    _ = ∫ g, X g * (P0 g - P1 g) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      ring

/-- Positive beta makes the true density-row Haar squared distance
strictly positive. The authentic two-Wilson-posterior expectation
difference is precisely this distance times GB's source overlap.
This identity is before any H- or beta-limit. -/
theorem p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta (le_of_lt hbeta) f e z =
    p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta (le_of_lt hbeta) f e z *
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta (le_of_lt hbeta) z.2 e := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta (le_of_lt hbeta) f e
  let D := p4Q2GB_originalWilsonPosteriorLeftDensityContrast
    H beta (le_of_lt hbeta) z.2 e
  let Q := p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    H beta (le_of_lt hbeta) z.2 e
  have hQPos : 0 < Q :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H beta hbeta z.2 e
  rw [p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing]
  change (∫ g, B (z,g) * D g ∂μ) =
    ((∫ g, B (z,g) * D g ∂μ) / Q) * Q
  exact (div_mul_cancel₀ _ hQPos.ne').symm

/-- At each genuine physical background, a zero original two-posterior
signed expectation gap is equivalent to a zero genuine source/contrast
projection coefficient, because its GA variance denominator is nonzero. -/
theorem p4Q2GI_originalWilsonSignedExpectationGap_zero_iff_projection_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta (le_of_lt hbeta) f e z = 0 ↔
      p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z = 0 := by
  have hQ : 0 <
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta (le_of_lt hbeta) z.2 e :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H beta hbeta z.2 e
  rw [p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
    H beta hbeta f e z]
  constructor
  · intro hZero
    exact (mul_eq_zero.mp hZero).resolve_right hQ.ne'
  · intro hZero
    rw [hZero, zero_mul]

/-- The finite original physical Wilson source/contrast link mass is zero
IFF the SIGNED physical source has equal true conditional posterior
expectations at the original identity and pi-rotated left boundaries,
pair-Haar-almost everywhere in the original OUTER context. -/
theorem p4Q2GI_originalWilsonSourceLinkMass_zero_iff_expectationGap_ae_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
      H beta (le_of_lt hbeta) f e = 0 ↔
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta (le_of_lt hbeta) f e z = 0 := by
  rw [p4Q2GH_originalWilsonSourceProjectedLinkMean_zero_iff_ae
    H beta hbeta f e]
  constructor
  · intro hAE
    filter_upwards [hAE] with z hz
    exact (p4Q2GI_originalWilsonSignedExpectationGap_zero_iff_projection_zero
      H beta hbeta f e z).mpr hz
  · intro hAE
    filter_upwards [hAE] with z hz
    exact (p4Q2GI_originalWilsonSignedExpectationGap_zero_iff_projection_zero
      H beta hbeta f e z).mp hz

/-- Actual physical Gram-null implies no true two-left-boundary Wilson
posterior signed-response expectation gap at ANY genuine spatial link,
pair-Haar-almost everywhere. This is a necessary obstruction,
not a claim that the original Wilson Gram is necessarily singular. -/
theorem p4Q2GI_originalWilsonGram_zero_implies_allLinkExpectationGap_ae_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ)
    (hZero : star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
        beta (le_of_lt hbeta)
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver
          H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) = 0) :
    ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H),
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i) e z = 0 := by
  intro e
  have hAELink :=
    p4Q2GH_originalWilsonGram_zero_implies_allLinkAEObstruction
      H beta hbeta f a hZero e
  filter_upwards [hAELink] with z hz
  exact (p4Q2GI_originalWilsonSignedExpectationGap_zero_iff_projection_zero
    H beta hbeta (∑ i : ι, a i • f i) e z).mpr hz

/-- A nontrivial difference in original interacting Wilson CONDITIONAL
expectations for the same signed physical source on one actual spatial
link on a positive-measure set gives STRICTLY POSITIVE original physical
Gram Rayleigh. No point-mass Haar atom is used. -/
theorem p4Q2GI_originalWilsonPhysicalGram_pos_of_oneLink_expectationGap_notAEZero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDetect : ¬ ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta (le_of_lt hbeta) (∑ i : ι, a i • f i) e z = 0) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
        beta (le_of_lt hbeta)
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver
          H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  have hAlphaNotAE : ¬ ∀ᵐ z
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) (∑ i : ι, a i • f i) e z = 0 := by
    intro hAlphaAE
    apply hDetect
    filter_upwards [hAlphaAE] with z hz
    exact (p4Q2GI_originalWilsonSignedExpectationGap_zero_iff_projection_zero
      H beta hbeta (∑ i : ι, a i • f i) e z).mpr hz
  exact p4Q2GH_originalWilsonPhysicalGram_pos_of_oneLink_notAEZero
    H beta hbeta f a e hAlphaNotAE

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GI_originalWilsonSignedExpectationGap_zero_iff_projection_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GI_originalWilsonSourceLinkMass_zero_iff_expectationGap_ae_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GI_originalWilsonGram_zero_implies_allLinkExpectationGap_ae_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GI_originalWilsonPhysicalGram_pos_of_oneLink_expectationGap_notAEZero
