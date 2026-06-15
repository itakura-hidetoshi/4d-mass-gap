import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteOSPropertyTransfer
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
theorem finite_wilson_single_source_countableSkeleton_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β) :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure := by
  change S.continuumMeasure = R.continuumMeasure
  exact finite_wilson_gibbs_single_source_constructed_unique R
    S.continuumMeasure S.isProjectiveLimit

/-- Transport the four theorem-generated OS analytic properties from the
explicit common-source Wilson law to an equal countable-skeleton realization. -/
noncomputable def finite_wilson_single_source_countableSkeleton_analyticTransferData
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      S.projectiveLimitMeasure :=
  D.rebaseLimit (finite_wilson_single_source_countableSkeleton_eq_explicit R S)

/-- The countable-skeleton analytic construction uses exactly the explicit
finite Wilson continuum law. -/
theorem finite_wilson_single_source_countableSkeleton_transfer_measure
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    (finite_wilson_single_source_countableSkeleton_analyticTransferData R S D)
        .toContinuumConstruction.limit.continuumMeasure =
      R.continuumMeasure := by
  change S.continuumMeasure = R.continuumMeasure
  exact finite_wilson_gibbs_single_source_constructed_unique R
    S.continuumMeasure S.isProjectiveLimit

/-- Reflection positivity, Euclidean invariance, clustering, and regularity all
remain available after transport to the countable-skeleton projective limit. -/
theorem finite_wilson_single_source_countableSkeleton_transfer_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    (finite_wilson_single_source_countableSkeleton_analyticTransferData R S D)
        .toContinuumConstruction.toMeasurePackage.ready := by
  simpa only [finite_wilson_single_source_countableSkeleton_analyticTransferData]
    using euclidean_yang_mills_projective_limit_rebase_ready D
      (finite_wilson_single_source_countableSkeleton_eq_explicit R S)

/-- Explicit common-source, standard-Borel, compact-tightness, and countable
skeleton realizations are simultaneously OS/Wightman ready from one analytic
limit-transfer datum. -/
theorem finite_wilson_single_source_four_route_transfer_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    D.toContinuumConstruction.toMeasurePackage.ready ∧
      (finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
          R D).toContinuumConstruction.toMeasurePackage.ready ∧
      (finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
          R D).toContinuumConstruction.toMeasurePackage.ready ∧
      (finite_wilson_single_source_countableSkeleton_analyticTransferData R S D)
        .toContinuumConstruction.toMeasurePackage.ready :=
  ⟨euclidean_yang_mills_projective_limit_transferred_measure_package_ready D,
    finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_ready R D,
    finite_wilson_single_source_finiteDiscrete_compactTight_transfer_ready R D,
    finite_wilson_single_source_countableSkeleton_transfer_ready R S D⟩

/-- All four theorem-generated analytic constructions have exactly the explicit
common-source Wilson continuum measure. -/
theorem finite_wilson_single_source_four_route_transfer_measures
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    D.toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
          R D).toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
          R D).toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finite_wilson_single_source_countableSkeleton_analyticTransferData R S D)
        .toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure :=
  ⟨rfl,
    finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_measure R D,
    finite_wilson_single_source_finiteDiscrete_compactTight_transfer_measure R D,
    finite_wilson_single_source_countableSkeleton_transfer_measure R S D⟩

end

end MathlibAnalytic
end MGAP4D
