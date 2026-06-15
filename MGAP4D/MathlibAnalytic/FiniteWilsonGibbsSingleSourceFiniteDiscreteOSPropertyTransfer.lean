import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransferRebase

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Transport analytic limit data from the explicit common-source Wilson law to
its equal Standard-Borel projective-limit realization. -/
noncomputable def
    finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.finiteDiscreteStandardBorelLimit :=
  D.rebaseLimit
    (finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R)

/-- Transport analytic limit data from the explicit common-source Wilson law to
its equal compact-tightness projective-limit realization. -/
noncomputable def
    finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.finiteDiscreteCompactTightLimit :=
  D.rebaseLimit
    (finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R)

/-- The Standard-Borel analytic construction uses exactly the explicit
`globalObserve` continuum Wilson law. -/
theorem finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_measure
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    (finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
        R D).toContinuumConstruction.limit.continuumMeasure =
      R.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R

/-- The compact-tightness analytic construction uses exactly the explicit
`globalObserve` continuum Wilson law. -/
theorem finite_wilson_single_source_finiteDiscrete_compactTight_transfer_measure
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    (finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
        R D).toContinuumConstruction.limit.continuumMeasure =
      R.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R

/-- The theorem-generated OS properties remain ready after transport to the
Standard-Borel projective-limit law. -/
theorem finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_ready
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    (finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
        R D).toContinuumConstruction.toMeasurePackage.ready := by
  simpa only [
    finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData]
    using euclidean_yang_mills_projective_limit_rebase_ready D
      (finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R)

/-- The theorem-generated OS properties remain ready after transport to the
compact-tightness projective-limit law. -/
theorem finite_wilson_single_source_finiteDiscrete_compactTight_transfer_ready
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    (finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
        R D).toContinuumConstruction.toMeasurePackage.ready := by
  simpa only [
    finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData]
    using euclidean_yang_mills_projective_limit_rebase_ready D
      (finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R)

/-- Explicit common-source, Standard-Borel, and compact-tightness realizations
all carry ready OS/Wightman measure packages from the same analytic limit data. -/
theorem finite_wilson_single_source_finiteDiscrete_three_route_transfer_ready
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    D.toContinuumConstruction.toMeasurePackage.ready ∧
      (finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
          R D).toContinuumConstruction.toMeasurePackage.ready ∧
      (finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
          R D).toContinuumConstruction.toMeasurePackage.ready :=
  ⟨euclidean_yang_mills_projective_limit_transferred_measure_package_ready D,
    finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_ready R D,
    finite_wilson_single_source_finiteDiscrete_compactTight_transfer_ready R D⟩

/-- The three analytic constructions have one and the same continuum measure,
namely the explicit pushforward of the finite Wilson Gibbs source. -/
theorem finite_wilson_single_source_finiteDiscrete_three_route_transfer_measures
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure) :
    D.toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData
          R D).toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData
          R D).toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure :=
  ⟨rfl,
    finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_measure R D,
    finite_wilson_single_source_finiteDiscrete_compactTight_transfer_measure R D⟩

end

end MathlibAnalytic
end MGAP4D
