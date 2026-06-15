import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveMarginals
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCommonProbabilityRealizationProjectiveLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The global field configuration read from a fixed finite Wilson configuration.
The value at `x` is defined by the already available singleton observation. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.globalObserve
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    (W.system R.sourceScale).Configuration →
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration :=
  fun A x =>
    R.observe ({x} : Finset EuclideanFourSpace) A
      (⟨x, by simp⟩ : ↥({x} : Finset EuclideanFourSpace))

/-- The global observation is measurable because each singleton observation is
measurable and the continuum configuration space carries the product measurable
structure. -/
theorem finite_wilson_gibbs_single_source_globalObserve_measurable
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    Measurable R.globalObserve := by
  exact measurable_pi_lambda _ (fun x =>
    (measurable_pi_apply
      (⟨x, by simp⟩ : ↥({x} : Finset EuclideanFourSpace))).comp
        (R.observe_measurable ({x} : Finset EuclideanFourSpace)))

/-- Restricting the global observation to a finite set recovers the original
finite-dimensional observation.  This is where the finite-observation
compatibility hypothesis is used. -/
theorem finite_wilson_gibbs_single_source_globalObserve_restrict
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    (A : (W.system R.sourceScale).Configuration) :
    J.restrict (R.globalObserve A) = R.observe J A := by
  funext j
  have hsingleton : ({j.1} : Finset EuclideanFourSpace) ⊆ J := by
    simpa using j.2
  have hcompat :=
    R.observe_restrict J ({j.1} : Finset EuclideanFourSpace)
      hsingleton A
  have hpoint := congrFun hcompat
    (⟨j.1, by simp⟩ : ↥({j.1} : Finset EuclideanFourSpace))
  change
    R.observe ({j.1} : Finset EuclideanFourSpace) A
        (⟨j.1, by simp⟩ : ↥({j.1} : Finset EuclideanFourSpace)) =
      R.observe J A j
  simpa [Finset.restrict₂] using hpoint

/-- The fixed finite Wilson Gibbs configuration space simultaneously realizes
all finite-dimensional marginal laws. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.toCommonProbabilityRealization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    EuclideanYangMillsCommonProbabilityRealization
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  { sampleSpace := (W.system R.sourceScale).Configuration
    sampleMeasurableSpace := inferInstance
    sourceMeasure := (W.system R.sourceScale).gibbsMeasure
    sourceProbability := inferInstance
    globalField := R.globalObserve
    globalField_measurable :=
      finite_wilson_gibbs_single_source_globalObserve_measurable R
    finiteLaw := by
      intro J
      change
        (W.system R.sourceScale).gibbsMeasure.map
            (fun A => J.restrict (R.globalObserve A)) =
          (W.system R.sourceScale).gibbsMeasure.map (R.observe J)
      apply congrArg (fun f =>
        (W.system R.sourceScale).gibbsMeasure.map f)
      funext A
      exact finite_wilson_gibbs_single_source_globalObserve_restrict R J A }

/-- The additional common-realization hypothesis is satisfied by every
single-source Wilson Gibbs realization. -/
theorem finite_wilson_gibbs_single_source_common_realization_exists
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    Nonempty
      (EuclideanYangMillsCommonProbabilityRealization
        R.toProjectiveRealization.toProjectiveCylinderFamily) :=
  ⟨R.toCommonProbabilityRealization⟩

/-- Explicit continuum measure: push the normalized finite Wilson Gibbs measure
forward through the global observation map. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.continuumMeasure
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    Measure R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration :=
  (W.system R.sourceScale).gibbsMeasure.map R.globalObserve

/-- The explicit Wilson pushforward agrees definitionally with the continuum
measure supplied by the general common-realization theorem. -/
theorem finite_wilson_gibbs_single_source_continuumMeasure_eq_common_realization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    R.continuumMeasure = R.toCommonProbabilityRealization.continuumMeasure := by
  rfl

/-- The explicitly constructed pushforward measure realizes every finite Wilson
Gibbs marginal, hence is a Mathlib projective-limit measure. -/
theorem finite_wilson_gibbs_single_source_continuumMeasure_isProjectiveLimit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    IsProjectiveLimit R.continuumMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal := by
  rw [finite_wilson_gibbs_single_source_continuumMeasure_eq_common_realization R]
  exact R.toCommonProbabilityRealization.continuumMeasure_isProjectiveLimit

/-- The explicit projective-limit measure object. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.projectiveLimitMeasure
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  { continuumMeasure := R.continuumMeasure
    projectiveLimit :=
      finite_wilson_gibbs_single_source_continuumMeasure_isProjectiveLimit R }

/-- Existence of a measure realizing all finite-dimensional Wilson Gibbs
marginals.  This is the common-realization existence theorem specialized to the
Wilson Gibbs source. -/
theorem finite_wilson_gibbs_single_source_projective_limit_exists
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal := by
  exact euclidean_yang_mills_projective_limit_exists_of_common_realization
    R.toCommonProbabilityRealization

/-- Equivalent structure-level existence statement. -/
theorem finite_wilson_gibbs_single_source_projective_limit_nonempty
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    Nonempty
      (EuclideanYangMillsProjectiveLimitMeasure
        R.toProjectiveRealization.toProjectiveCylinderFamily) :=
  ⟨R.projectiveLimitMeasure⟩

/-- The explicitly constructed projective limit is a probability measure. -/
theorem finite_wilson_gibbs_single_source_continuumMeasure_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    IsProbabilityMeasure R.continuumMeasure := by
  rw [finite_wilson_gibbs_single_source_continuumMeasure_eq_common_realization R]
  exact R.toCommonProbabilityRealization.continuumMeasure_probability

/-- Every measurable cylinder of the constructed continuum measure is exactly a
finite Wilson Gibbs probability. -/
theorem finite_wilson_gibbs_single_source_constructed_cylinder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    R.continuumMeasure (cylinder J s) =
      (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s) := by
  exact finite_wilson_gibbs_single_source_projective_limit_cylinder
    R R.projectiveLimitMeasure J hs

/-- The constructed measure is the unique projective limit of the concrete
finite Wilson marginal family. -/
theorem finite_wilson_gibbs_single_source_constructed_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν = R.continuumMeasure := by
  exact euclidean_yang_mills_projective_limit_unique
    R.projectiveLimitMeasure ν hν

end

end MathlibAnalytic
end MGAP4D
