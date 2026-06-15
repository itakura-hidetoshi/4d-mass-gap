import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceOSPropertyRouteTransfer
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCountableSkeletonExtension

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- Any countable standard-Borel skeleton reconstruction recovering the finite
Wilson laws is the same continuum law as the explicit common-source
`globalObserve` pushforward. -/
theorem finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β) :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure := by
  change S.continuumMeasure = R.continuumMeasure
  exact finite_wilson_gibbs_single_source_constructed_unique R
    S.continuumMeasure S.isProjectiveLimit

/-- Transport the theorem-generated OS analytic limit data from the explicit
Wilson projective limit to an equal countable-skeleton projective limit. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.countableSkeletonOSAnalyticTransferData
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      S.projectiveLimitMeasure :=
  D.rebaseLimit
    (finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S)

/-- Continuum construction on the countable-skeleton law carrying reflection
positivity, Euclidean invariance, clustering, and regularity inherited from the
explicit Wilson route. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.countableSkeletonOSContinuumConstruction
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  (R.countableSkeletonOSAnalyticTransferData S D).toContinuumConstruction

/-- The countable-skeleton analytic construction uses exactly the explicit
finite Wilson continuum law. -/
theorem finite_wilson_single_source_countableSkeleton_os_measure_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.countableSkeletonOSContinuumConstruction S D).limit.continuumMeasure =
      R.continuumMeasure := by
  change S.projectiveLimitMeasure.continuumMeasure =
    R.projectiveLimitMeasure.continuumMeasure
  exact finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S

/-- Reflection positivity, Euclidean invariance, clustering, and regularity all
remain available after transport to the countable-skeleton projective limit. -/
theorem finite_wilson_single_source_countableSkeleton_os_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.countableSkeletonOSContinuumConstruction S D).toMeasurePackage.ready := by
  simpa only [
    FiniteWilsonGibbsSingleSourceProjectiveRealization.countableSkeletonOSContinuumConstruction,
    FiniteWilsonGibbsSingleSourceProjectiveRealization.countableSkeletonOSAnalyticTransferData]
    using euclidean_yang_mills_projective_limit_rebase_ready D
      (finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S)

/-- Explicit common-source, standard-Borel, compact-tightness, and countable-
skeleton constructions are simultaneously ready for OS/Wightman reconstruction. -/
theorem finite_wilson_single_source_four_os_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S D).toMeasurePackage.ready := by
  rcases finite_wilson_single_source_three_os_routes_ready R D with
    ⟨hExplicit, hStandardBorel, hCompactTight⟩
  exact ⟨hExplicit, hStandardBorel, hCompactTight,
    finite_wilson_single_source_countableSkeleton_os_ready R S D⟩

/-- All four theorem-generated analytic constructions have exactly the explicit
common-source Wilson continuum measure. -/
theorem finite_wilson_single_source_four_os_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S D).limit.continuumMeasure =
        R.continuumMeasure := by
  rcases finite_wilson_single_source_three_os_route_measures_eq_explicit R D with
    ⟨hExplicit, hStandardBorel, hCompactTight⟩
  exact ⟨hExplicit, hStandardBorel, hCompactTight,
    finite_wilson_single_source_countableSkeleton_os_measure_eq_explicit R S D⟩

end

end MathlibAnalytic
end MGAP4D
