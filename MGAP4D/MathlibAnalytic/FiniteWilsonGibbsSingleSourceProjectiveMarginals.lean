import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A projective family of finite-dimensional observables read from one fixed
finite Wilson Gibbs measure.

All marginals use the same source lattice.  Projectivity therefore follows only
from compatibility of the observation maps under coordinate restriction; no
deterministic Gibbs-preserving coarse-graining map is required. -/
structure FiniteWilsonGibbsSingleSourceProjectiveRealization
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  fieldValue : EuclideanFourSpace → Type
  [fieldValueMeasurableSpace :
    ∀ x, MeasurableSpace (fieldValue x)]
  sourceScale : W.index
  observe :
    ∀ J : Finset EuclideanFourSpace,
      (W.system sourceScale).Configuration →
        (∀ x : J, fieldValue x)
  observe_measurable : ∀ J, Measurable (observe J)
  observe_restrict :
    ∀ (I J : Finset EuclideanFourSpace) (hJI : J ⊆ I)
      (A : (W.system sourceScale).Configuration),
      observe J A = Finset.restrict₂ hJI (observe I A)

attribute [instance]
  FiniteWilsonGibbsSingleSourceProjectiveRealization.fieldValueMeasurableSpace

/-- Finite-dimensional marginal obtained by pushing one fixed Wilson Gibbs
measure through the compatible observation map for `J`. -/
noncomputable def FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteMarginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace) :
    Measure (∀ x : J, R.fieldValue x) :=
  (W.system R.sourceScale).gibbsMeasure.map (R.observe J)

/-- Compatibility of observations from one common Gibbs source implies
projective consistency of their pushforward laws. -/
theorem finite_wilson_gibbs_single_source_projective
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    IsProjectiveMeasureFamily R.finiteMarginal := by
  intro I J hJI
  let μ := (W.system R.sourceScale).gibbsMeasure
  let oI := R.observe I
  let oJ := R.observe J
  let r : (∀ x : I, R.fieldValue x) → (∀ x : J, R.fieldValue x) :=
    Finset.restrict₂ hJI
  have hoI : Measurable oI := R.observe_measurable I
  have hr : Measurable r :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  change μ.map oJ = (μ.map oI).map r
  calc
    μ.map oJ = μ.map (r ∘ oI) := by
      apply congrArg (fun f => μ.map f)
      funext A
      exact R.observe_restrict I J hJI A
    _ = (μ.map oI).map r := (Measure.map_map hr hoI).symm

/-- Package the single-source construction as the concrete Wilson Gibbs
projective realization used by the continuum layer. -/
def FiniteWilsonGibbsSingleSourceProjectiveRealization.toProjectiveRealization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    FiniteWilsonGibbsProjectiveRealization W :=
  { fieldValue := R.fieldValue
    fieldValueMeasurableSpace := R.fieldValueMeasurableSpace
    scale := fun _ => R.sourceScale
    observe := R.observe
    observe_measurable := R.observe_measurable
    pushforward_projective := finite_wilson_gibbs_single_source_projective R }

/-- Every single-source marginal is a probability measure. -/
theorem finite_wilson_gibbs_single_source_marginal_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace) :
    IsProbabilityMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) := by
  exact finite_wilson_gibbs_projective_marginal_probability
    R.toProjectiveRealization J

/-- The measurable cylinder content is exactly the probability of the
observation preimage in the fixed Wilson Gibbs measure. -/
theorem finite_wilson_gibbs_single_source_cylinder_content
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.cylinderContent
        (cylinder J s) =
      (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_cylinder_content_eq_gibbs_preimage
    R.toProjectiveRealization J hs

/-- Once a projective-limit measure is supplied, all of its measurable cylinder
probabilities are represented by the fixed finite Wilson Gibbs source. -/
theorem finite_wilson_gibbs_single_source_projective_limit_cylinder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (L : EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    L.continuumMeasure (cylinder J s) =
      (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_projective_limit_cylinder_eq_gibbs_preimage
    R.toProjectiveRealization L J hs

/-- Audit-visible certificate for the single common Gibbs source route. -/
structure FiniteWilsonGibbsSingleSourceProjectiveCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  observationCompatibility :
    ∀ (I J : Finset EuclideanFourSpace) (hJI : J ⊆ I)
      (A : (W.system R.sourceScale).Configuration),
      R.observe J A = Finset.restrict₂ hJI (R.observe I A)
  projectiveMarginals :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal
  marginalProbability :
    ∀ J : Finset EuclideanFourSpace,
      IsProbabilityMeasure
        (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J)

/-- Construct the single-source projectivity certificate. -/
def finiteWilsonGibbsSingleSourceProjectiveCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    FiniteWilsonGibbsSingleSourceProjectiveCertificate R :=
  { observationCompatibility := R.observe_restrict
    projectiveMarginals := finite_wilson_gibbs_single_source_projective R
    marginalProbability :=
      finite_wilson_gibbs_single_source_marginal_probability R }

end

end MathlibAnalytic
end MGAP4D
