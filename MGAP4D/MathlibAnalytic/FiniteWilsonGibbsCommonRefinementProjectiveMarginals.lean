import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A common-refinement realization of finite Wilson Gibbs marginals.

For every inclusion `J ⊆ I`, a common finite Wilson system is chosen together
with measurable maps to the systems used for `I` and `J`.  Both target Gibbs
measures are pushforwards of the common Gibbs measure, and the two observation
routes commute after restricting the `I`-observation to `J`.

This formulation is weaker and more natural than requiring a deterministic
Gibbs-preserving map directly from the `I`-system to the `J`-system. -/
structure FiniteWilsonGibbsCommonRefinementRealization
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  fieldValue : EuclideanFourSpace → Type
  [fieldValueMeasurableSpace :
    ∀ x, MeasurableSpace (fieldValue x)]
  scale : Finset EuclideanFourSpace → W.index
  observe :
    ∀ J : Finset EuclideanFourSpace,
      (W.system (scale J)).Configuration →
        (∀ x : J, fieldValue x)
  observe_measurable : ∀ J, Measurable (observe J)
  commonScale :
    ∀ (I J : Finset EuclideanFourSpace), J ⊆ I → W.index
  refineToLarge :
    ∀ (I J : Finset EuclideanFourSpace) (hJI : J ⊆ I),
      (W.system (commonScale I J hJI)).Configuration →
        (W.system (scale I)).Configuration
  refineToSmall :
    ∀ (I J : Finset EuclideanFourSpace) (hJI : J ⊆ I),
      (W.system (commonScale I J hJI)).Configuration →
        (W.system (scale J)).Configuration
  refineToLarge_measurable :
    ∀ I J hJI, Measurable (refineToLarge I J hJI)
  refineToSmall_measurable :
    ∀ I J hJI, Measurable (refineToSmall I J hJI)
  commonPushforwardToLarge :
    ∀ I J hJI,
      (W.system (commonScale I J hJI)).gibbsMeasure.map
          (refineToLarge I J hJI) =
        (W.system (scale I)).gibbsMeasure
  commonPushforwardToSmall :
    ∀ I J hJI,
      (W.system (commonScale I J hJI)).gibbsMeasure.map
          (refineToSmall I J hJI) =
        (W.system (scale J)).gibbsMeasure
  observe_commonRefinement :
    ∀ I J hJI
      (A : (W.system (commonScale I J hJI)).Configuration),
      observe J (refineToSmall I J hJI A) =
        Finset.restrict₂ hJI (observe I (refineToLarge I J hJI A))

attribute [instance]
  FiniteWilsonGibbsCommonRefinementRealization.fieldValueMeasurableSpace

/-- The finite-dimensional law obtained from the Wilson Gibbs measure selected
for a finite set of spacetime points. -/
noncomputable def FiniteWilsonGibbsCommonRefinementRealization.finiteMarginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (J : Finset EuclideanFourSpace) :
    Measure (∀ x : J, R.fieldValue x) :=
  (W.system (R.scale J)).gibbsMeasure.map (R.observe J)

/-- A common-refinement diagram proves projective consistency of the concrete
finite Wilson Gibbs pushforward laws. -/
theorem finite_wilson_gibbs_common_refinement_projective
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W) :
    IsProjectiveMeasureFamily R.finiteMarginal := by
  intro I J hJI
  let μK := (W.system (R.commonScale I J hJI)).gibbsMeasure
  let μI := (W.system (R.scale I)).gibbsMeasure
  let μJ := (W.system (R.scale J)).gibbsMeasure
  let pI := R.refineToLarge I J hJI
  let pJ := R.refineToSmall I J hJI
  let oI := R.observe I
  let oJ := R.observe J
  let r : (∀ x : I, R.fieldValue x) → (∀ x : J, R.fieldValue x) :=
    Finset.restrict₂ hJI
  have hpI : Measurable pI := R.refineToLarge_measurable I J hJI
  have hpJ : Measurable pJ := R.refineToSmall_measurable I J hJI
  have hoI : Measurable oI := R.observe_measurable I
  have hoJ : Measurable oJ := R.observe_measurable J
  have hr : Measurable r :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  change μJ.map oJ = (μI.map oI).map r
  calc
    μJ.map oJ = (μK.map pJ).map oJ := by
      rw [R.commonPushforwardToSmall I J hJI]
    _ = μK.map (oJ ∘ pJ) := Measure.map_map hoJ hpJ
    _ = μK.map ((r ∘ oI) ∘ pI) := by
      apply congrArg (fun f => μK.map f)
      funext A
      exact R.observe_commonRefinement I J hJI A
    _ = (μK.map pI).map (r ∘ oI) :=
      (Measure.map_map (hr.comp hoI) hpI).symm
    _ = μI.map (r ∘ oI) := by
      rw [R.commonPushforwardToLarge I J hJI]
    _ = (μI.map oI).map r :=
      (Measure.map_map hr hoI).symm

/-- Package the common-refinement construction as the finite-dimensional
projective family used by the continuum layer. -/
def FiniteWilsonGibbsCommonRefinementRealization.toProjectiveRealization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W) :
    FiniteWilsonGibbsProjectiveRealization W :=
  { fieldValue := R.fieldValue
    fieldValueMeasurableSpace := R.fieldValueMeasurableSpace
    scale := R.scale
    observe := R.observe
    observe_measurable := R.observe_measurable
    pushforward_projective :=
      finite_wilson_gibbs_common_refinement_projective R }

/-- The resulting finite-dimensional distributions are normalized probability
measures. -/
theorem finite_wilson_gibbs_common_refinement_marginal_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (J : Finset EuclideanFourSpace) :
    IsProbabilityMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) := by
  exact finite_wilson_gibbs_projective_marginal_probability
    R.toProjectiveRealization J

/-- The common-refinement construction determines the measurable cylinder
content by concrete finite Wilson Gibbs probabilities. -/
theorem finite_wilson_gibbs_common_refinement_cylinder_content
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.cylinderContent
        (cylinder J s) =
      (W.system (R.scale J)).gibbsMeasure
        ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_cylinder_content_eq_gibbs_preimage
    R.toProjectiveRealization J hs

/-- Once a projective-limit measure is supplied, every measurable continuum
cylinder has the finite Wilson Gibbs probability selected by the common-
refinement realization. -/
theorem finite_wilson_gibbs_common_refinement_projective_limit_cylinder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (L : EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    L.continuumMeasure (cylinder J s) =
      (W.system (R.scale J)).gibbsMeasure
        ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_projective_limit_cylinder_eq_gibbs_preimage
    R.toProjectiveRealization L J hs

/-- Audit-visible common-refinement certificate. -/
structure FiniteWilsonGibbsCommonRefinementCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W) where
  commonToLargePreservesLaw :
    ∀ I J hJI,
      (W.system (R.commonScale I J hJI)).gibbsMeasure.map
          (R.refineToLarge I J hJI) =
        (W.system (R.scale I)).gibbsMeasure
  commonToSmallPreservesLaw :
    ∀ I J hJI,
      (W.system (R.commonScale I J hJI)).gibbsMeasure.map
          (R.refineToSmall I J hJI) =
        (W.system (R.scale J)).gibbsMeasure
  observationDiagramCommutes :
    ∀ I J hJI
      (A : (W.system (R.commonScale I J hJI)).Configuration),
      R.observe J (R.refineToSmall I J hJI A) =
        Finset.restrict₂ hJI
          (R.observe I (R.refineToLarge I J hJI A))
  projectiveMarginals :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal
  marginalProbability :
    ∀ J : Finset EuclideanFourSpace,
      IsProbabilityMeasure
        (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J)

/-- Construct the common-refinement projectivity certificate. -/
def finiteWilsonGibbsCommonRefinementCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W) :
    FiniteWilsonGibbsCommonRefinementCertificate R :=
  { commonToLargePreservesLaw := R.commonPushforwardToLarge
    commonToSmallPreservesLaw := R.commonPushforwardToSmall
    observationDiagramCommutes := R.observe_commonRefinement
    projectiveMarginals :=
      finite_wilson_gibbs_common_refinement_projective R
    marginalProbability :=
      finite_wilson_gibbs_common_refinement_marginal_probability R }

end

end MathlibAnalytic
end MGAP4D
