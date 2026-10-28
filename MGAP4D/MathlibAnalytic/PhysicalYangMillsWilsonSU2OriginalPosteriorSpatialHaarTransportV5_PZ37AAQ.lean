import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorSpatialTranslationOrbitsV5_PZ37AAP
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAQ — original spatial Haar transport and posterior integrand bridge

The translation orbits in AAP are those of ACTUAL time-zero links on the
original even-periodic Wilson lattice, not a proxy finite graph.

This module proves unconditional, measure-theoretic spatial transport for
the original full SU(2) spatial-configuration product Haar, and for the
original boundary PAIR-Haar law. It also identifies how translating the
actual configuration commutes with physical right-link insertion and
the genuine pi-rotated left boundary at the translated link.

Finally, we prove a precisely typed descent statement: pointwise covariance
of the ORIGINAL GL squared Wilson posterior gap divided by the ORIGINAL FX
Wilson density-contrast variance implies covariance of the SAME AAK original
integrated posterior response, hence the conditional AAP bounds. An
equivalent sufficient pair of inputs states covariance of GI's two ORIGINAL
conditional Wilson posterior expectation gaps and covariance of FX's ORIGINAL
variance. These inputs are NOT asserted: proving their invariance requires
transport of both interacting conditional Wilson laws and of the unchanged
centered Gauss-law source (including the physical vacuum factor).

Thus the two Haar-law transport obligations are discharged without making
the much stronger original-posterior invariance assumption. No surrogate
Haar conditional, no new axioms, no sorry/admit/native_decide, no new
positive-fine interval, E/F, H1-H4, or continuum mass gap. Append-only.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAQ_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAQ_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAQ_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAQ_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAQ_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AAQ_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G
private noncomputable instance p4Q2PZ37AAQ_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalSpatialHaarTransport
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pairHaar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Exactly the original spatial-link coordinate permutation of the
existing genuine SU(2) configuration, implemented as a measurable
equivalence, with no modification of link values. -/
noncomputable def p4Q2PZ37AAQ_originalSpatialConfigurationTranslation
    (a : Disp) : Cfg ≃ᵐ Cfg :=
  MeasurableEquiv.piCongrLeft (fun _ : Link => G)
    (p4Q2PZ37AAP_actualSpatialLinkTranslation H a)

/-- The translated configuration at the translated original link is
the old configuration at the old link. -/
@[simp] theorem p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink
    (a : Disp) (A : Cfg) (e : Link) :
    p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A
      (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) = A e := by
  simpa [p4Q2PZ37AAQ_originalSpatialConfigurationTranslation] using
    (Equiv.piCongrLeft_apply_apply
      (fun _ : Link => G)
      (p4Q2PZ37AAP_actualSpatialLinkTranslation H a) A e)

/-- Genuine original spatial-link insertion commutes exactly with
spatial reindexing. This is an equality of complete configurations. -/
theorem p4Q2PZ37AAQ_configurationTranslation_update
    (a : Disp) (A : Cfg) (e : Link) (g : G) :
    p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a
        (Function.update A e g) =
      Function.update
        (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A)
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) g := by
  classical
  funext f
  let T := p4Q2PZ37AAP_actualSpatialLinkTranslation H a
  obtain ⟨q, rfl⟩ := T.surjective f
  simp only [p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink]
  by_cases hq : q = e
  · subst q
    simp
  · have ht : T q ≠ T e := fun h => hq (T.injective h)
    simp [Function.update, hq, ht]

/-- The original constant identity LEFT Wilson boundary is fixed by
every true spatial translation. -/
theorem p4Q2PZ37AAQ_identityLeftBoundary_translation
    (a : Disp) :
    p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a
      (originalWilsonExplicitIdentityBoundary H) =
      originalWilsonExplicitIdentityBoundary H := by
  funext f
  let T := p4Q2PZ37AAP_actualSpatialLinkTranslation H a
  obtain ⟨e, rfl⟩ := T.surjective f
  rw [p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink]
  rfl

/-- The TRUE pi-rotation LEFT Wilson boundary follows its ORIGINAL
spatial link, with no gauge-fixed or Haar surrogate boundary. -/
theorem p4Q2PZ37AAQ_piRotatedLeftBoundary_translation
    (a : Disp) (e : Link) :
    p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) =
    p4Q2FQ_originalSU2LeftPiRotationAtLink H
      (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) := by
  unfold p4Q2FQ_originalSU2LeftPiRotationAtLink
  rw [p4Q2PZ37AAQ_configurationTranslation_update,
    p4Q2PZ37AAQ_identityLeftBoundary_translation]

/-- The ACTUAL full SU(2) product Haar probability on the complete
original spatial-slice link configuration is invariant under the
unconditional geometric translation constructed in AAP. -/
theorem p4Q2PZ37AAQ_originalSpatialHaar_measurePreserving
    (a : Disp) :
    MeasurePreserving
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a)
      haar haar := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  simpa [p4Q2PZ37AAQ_originalSpatialConfigurationTranslation] using
    (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Link => normalizedCompactHaar G)
      (p4Q2PZ37AAP_actualSpatialLinkTranslation H a))

/-- Both original outer boundary configurations are shifted by the
SAME original spatial translation; this is exactly the outer pair
used for the genuine GL/AAK posterior response. -/
noncomputable def p4Q2PZ37AAQ_originalSpatialPairTranslation
    (a : Disp) : Pair → Pair :=
  Prod.map
    (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a)
    (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a)

/-- The original OUTER pair-Haar measure is invariant. This theorem
does not change either of the two INNER interacting Wilson posteriors. -/
theorem p4Q2PZ37AAQ_originalPairHaar_measurePreserving
    (a : Disp) :
    MeasurePreserving
      (p4Q2PZ37AAQ_originalSpatialPairTranslation H a)
      pairHaar pairHaar := by
  have hp := p4Q2PZ37AAQ_originalSpatialHaar_measurePreserving H a
  simpa [p4Q2PZ37AAQ_originalSpatialPairTranslation,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
    using hp.prod hp

/-- Measure-preserving change of variables for an integrable REAL
function on the unchanged original outer boundary PAIR-Haar context. -/
theorem p4Q2PZ37AAQ_originalPairHaar_integralTranslation
    (a : Disp) (f : Pair → ℝ) (hf : Integrable f pairHaar) :
    (∫ z : Pair, f (p4Q2PZ37AAQ_originalSpatialPairTranslation H a z)
      ∂pairHaar) =
    (∫ z : Pair, f z ∂pairHaar) := by
  have hp := p4Q2PZ37AAQ_originalPairHaar_measurePreserving H a
  have hMeas :
      AEStronglyMeasurable f
        (Measure.map (p4Q2PZ37AAQ_originalSpatialPairTranslation H a)
          pairHaar) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  calc
    (∫ z : Pair, f (p4Q2PZ37AAQ_originalSpatialPairTranslation H a z)
      ∂pairHaar) =
      (∫ z : Pair, f z ∂
        Measure.map (p4Q2PZ37AAQ_originalSpatialPairTranslation H a)
          pairHaar) :=
        (MeasureTheory.integral_map hp.measurable.aemeasurable hMeas).symm
    _ = ∫ z : Pair, f z ∂pairHaar := by rw [hp.map_eq]

/-- The exact ORIGINAL two interacting Wilson-posterior expectation-gap
square divided by the original positive Wilson density contrast
variance, prior to integrating over the outer true pair-Haar law. -/
noncomputable def p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair) : ℝ :=
  (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 /
  p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    H b hb.le z.2 e

/-- The genuine original GL integrability theorem applies to the
unchanged, centered physical source at every original link. -/
theorem p4Q2PZ37AAQ_originalCenteredPosteriorFiber_integrable
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Integrable
      (p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb e)
      pairHaar := by
  exact p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
    H b hb (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e

/-- Exact integration bridge: pointwise covariance of the actual
two-posterior quotient in the genuine pair-Haar context suffices for
the AAP spatial covariance proposition. The remaining hypothesis is
the real Wilson posterior transport, not a Haar substitution. -/
theorem p4Q2PZ37AAQ_originalPosteriorCovariance_of_fiberCovariance
    (b : ℝ) (hb : 0 < b)
    (hFiber : ∀ (a : Disp) (e : Link) (z : Pair),
      p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e)
        (p4Q2PZ37AAQ_originalSpatialPairTranslation H a z) =
      p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb e z) :
    p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb := by
  intro a e
  unfold p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
  change
    (∫ z : Pair,
      p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) z ∂pairHaar) =
      (∫ z : Pair,
        p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb e z
        ∂pairHaar)
  calc
    (∫ z : Pair,
      p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) z ∂pairHaar) =
    (∫ z : Pair,
      p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e)
        (p4Q2PZ37AAQ_originalSpatialPairTranslation H a z)
      ∂pairHaar) :=
      (p4Q2PZ37AAQ_originalPairHaar_integralTranslation H a
        (p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb
          (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e))
        (p4Q2PZ37AAQ_originalCenteredPosteriorFiber_integrable H b hb
          (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e))).symm
    _ = (∫ z : Pair,
      p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand H b hb e z
        ∂pairHaar) := by
      apply integral_congr_ae
      filter_upwards with z
      exact hFiber a e z

/-- More concrete posterior-transport obligations: covariance of
the SAME original two conditional-Wilson-posterior expectation gap and
of the SAME genuine contrast variance. Both are original-model
quantities, with no artificial common density or substitute source. -/
theorem p4Q2PZ37AAQ_originalPosteriorCovariance_of_gap_and_variance
    (b : ℝ) (hb : 0 < b)
    (hGap : ∀ (a : Disp) (e : Link) (z : Pair),
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e)
        (p4Q2PZ37AAQ_originalSpatialPairTranslation H a z) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)
    (hVariance : ∀ (a : Disp) (e : Link) (z : Pair),
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le
        (p4Q2PZ37AAQ_originalSpatialPairTranslation H a z).2
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) =
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e) :
    p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb := by
  apply p4Q2PZ37AAQ_originalPosteriorCovariance_of_fiberCovariance H b hb
  intro a e z
  unfold p4Q2PZ37AAQ_originalCenteredPosteriorFiberIntegrand
  rw [hGap a e z, hVariance a e z]

end OriginalSpatialHaarTransport
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_configurationTranslation_update
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_identityLeftBoundary_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_piRotatedLeftBoundary_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_originalSpatialHaar_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_originalPairHaar_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_originalPairHaar_integralTranslation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_originalCenteredPosteriorFiber_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_originalPosteriorCovariance_of_fiberCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAQ_originalPosteriorCovariance_of_gap_and_variance
