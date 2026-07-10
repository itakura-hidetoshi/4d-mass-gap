import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceExactGapContinuumSpine
import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureExactGapConstructionSpineTheorems

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Theorem package for the finite-Wilson single-source exact-gap continuum spine.

This file verifies that the generated continuum measure retains its concrete
Wilson marginal origin and that the reduced spine reaches the full exact-gap,
threshold-separation, and unique mass-gap-witness endpoints.
-/

/-- The generated continuum construction has the standard typed projective-limit
certificate. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.continuumCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    EuclideanYangMillsProjectiveContinuumMeasureCertificate
      A.continuumConstruction :=
  euclideanYangMillsProjectiveContinuumMeasureCertificate
    A.continuumConstruction

/-- Every finite-dimensional marginal of the generated continuum measure is the
pushforward of the fixed finite Wilson Gibbs source. -/
theorem FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.recoversWilsonMarginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R)
    (J : Finset EuclideanFourSpace) :
    A.continuumConstruction.limit.continuumMeasure.map J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) := by
  calc
    A.continuumConstruction.limit.continuumMeasure.map J.restrict =
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J :=
      A.continuumCertificate.finiteMarginalsRecovered J
    _ = (W.system R.sourceScale).gibbsMeasure.map (R.observe J) := by
      rfl

/-- Every measurable cylinder event of the generated continuum law is computed
by the fixed finite Wilson Gibbs source. -/
theorem FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.cylinder_eq_WilsonGibbs
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    A.continuumConstruction.limit.continuumMeasure (cylinder J s) =
      (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_single_source_projective_limit_cylinder
    R A.continuumConstruction.limit J hs

/-- The actual finite Wilson family retains probability, gauge invariance,
reflection positivity, and finite-volume Euclidean covariance. -/
def FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.finiteVolumeCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (_A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    FiniteWilsonOSAutomaticMeasureCertificate W :=
  finiteWilsonOSAutomaticMeasureCertificate W

/-- The concrete assembly reaches the reduced exact-gap continuum theorem
endpoint. -/
theorem FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.reducedExactGapComplete
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    A.toExactGapConstructionSpine.toConstructionSpine.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal =
        sInf
          (A.toExactGapConstructionSpine.toConstructionSpine.definitionBridge.spine.model.energySpectrum \
            ({0} : Set ℝ)) ∧
      A.toExactGapConstructionSpine.toConstructionSpine.definitionBridge.spine.model.firstExcitation =
        exactGapValueReal ∧
      A.toExactGapConstructionSpine.toConstructionSpine.definitionBridge.spine.model.massGapValue =
        exactGapValueReal ∧
      euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
        A.toExactGapConstructionSpine.toConstructionSpine := by
  exact
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_complete
      A.toExactGapConstructionSpine

/-- The concrete finite-Wilson route inherits exact-threshold spectral
separation. -/
theorem FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      A.toExactGapConstructionSpine.toConstructionSpine := by
  exact
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactThresholdSeparation
      A.toExactGapConstructionSpine

/-- The concrete finite-Wilson route inherits uniqueness of the canonical
mass-gap witness. -/
theorem FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.uniqueMassGapWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
      A.toExactGapConstructionSpine.toConstructionSpine := by
  exact
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_uniqueMassGapWitness
      A.toExactGapConstructionSpine

/-- Audit-visible certificate for the concrete finite-Wilson-to-exact-gap route. -/
structure FiniteWilsonGibbsSingleSourceExactGapContinuumSpineCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) where
  finiteVolume : FiniteWilsonOSAutomaticMeasureCertificate W
  continuum :
    EuclideanYangMillsProjectiveContinuumMeasureCertificate
      A.continuumConstruction
  measureBridgeReady : A.measureBridge.measure.ready
  continuumLawExplicit :
    A.continuumConstruction.limit.continuumMeasure = R.continuumMeasure
  marginalsAreWilson :
    ∀ J : Finset EuclideanFourSpace,
      A.continuumConstruction.limit.continuumMeasure.map J.restrict =
        (W.system R.sourceScale).gibbsMeasure.map (R.observe J)
  reducedSpineReady : A.toExactGapConstructionSpine.limitReady
  fullSpineReady :
    A.toExactGapConstructionSpine.toConstructionSpine.limitReady
  thresholdSeparation :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      A.toExactGapConstructionSpine.toConstructionSpine
  uniqueMassGapWitness :
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
      A.toExactGapConstructionSpine.toConstructionSpine

/-- Canonical certificate for the concrete finite-Wilson-to-exact-gap route. -/
noncomputable def finiteWilsonGibbsSingleSourceExactGapContinuumSpineCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumSpineCertificate A where
  finiteVolume := A.finiteVolumeCertificate
  continuum := A.continuumCertificate
  measureBridgeReady := A.measureBridgeReady
  continuumLawExplicit := A.continuumMeasure_eq_explicit
  marginalsAreWilson := A.recoversWilsonMarginal
  reducedSpineReady :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_limitReady
      A.toExactGapConstructionSpine
  fullSpineReady :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_fullLimitReady
      A.toExactGapConstructionSpine
  thresholdSeparation := A.exactThresholdSeparation
  uniqueMassGapWitness := A.uniqueMassGapWitness

/-- Compact endpoint joining concrete Wilson marginals to the exact spectral-gap
package. -/
theorem finiteWilsonGibbsSingleSourceExactGapContinuumSpine_complete
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    A.measureBridge.measure.ready ∧
      IsProbabilityMeasure A.continuumConstruction.limit.continuumMeasure ∧
      A.continuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      A.toExactGapConstructionSpine.toConstructionSpine.definitionBridge.spine.model.hasMassGap ∧
      euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
        A.toExactGapConstructionSpine.toConstructionSpine := by
  exact ⟨
    A.measureBridgeReady,
    A.continuumCertificate.continuumProbability,
    A.continuumMeasure_eq_explicit,
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_hasMassGap
      A.toExactGapConstructionSpine,
    A.uniqueMassGapWitness⟩

end

end MathlibAnalytic
end MGAP4D
