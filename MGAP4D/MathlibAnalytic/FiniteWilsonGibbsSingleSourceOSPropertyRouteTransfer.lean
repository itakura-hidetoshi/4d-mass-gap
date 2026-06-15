import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransferRebase
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- The four OS analytic limit packages attached to the explicit common-source
Wilson projective-limit measure. -/
abbrev FiniteWilsonGibbsSingleSourceOSPropertyTransferData :=
  EuclideanYangMillsProjectiveLimitAnalyticTransferData
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The standard-Borel Wilson limit is the explicit common-source
projective-limit measure, at structure-measure level. -/
theorem finite_wilson_single_source_standardBorelLimit_eq_explicitLimit :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure := by
  change R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure
  exact finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R

/-- The compact-tight Wilson limit is the explicit common-source
projective-limit measure, at structure-measure level. -/
theorem finite_wilson_single_source_compactTightLimit_eq_explicitLimit :
    R.finiteDiscreteCompactTightLimit.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure := by
  change R.finiteDiscreteCompactTightLimit.continuumMeasure = R.continuumMeasure
  exact finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R

/-- Explicit common-source Wilson continuum construction carrying reflection
positivity, Euclidean invariance, clustering, and regularity obtained by limit
transfer. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.explicitOSContinuumConstruction
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  D.toContinuumConstruction

/-- Rebase all four transferred OS properties to the standard-Borel
Kolmogorov construction. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.standardBorelOSContinuumConstruction
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  (D.rebaseLimit
    (finite_wilson_single_source_standardBorelLimit_eq_explicitLimit R)).toContinuumConstruction

/-- Rebase all four transferred OS properties to the compact-tightness
construction. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.compactTightOSContinuumConstruction
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  (D.rebaseLimit
    (finite_wilson_single_source_compactTightLimit_eq_explicitLimit R)).toContinuumConstruction

/-- The explicit route is ready for the OS/Wightman bridge. -/
theorem finite_wilson_single_source_explicit_os_ready
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).toMeasurePackage.ready :=
  euclidean_yang_mills_projective_limit_transferred_measure_package_ready D

/-- The standard-Borel route inherits the same four OS properties and is ready
for the OS/Wightman bridge. -/
theorem finite_wilson_single_source_standardBorel_os_ready
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.standardBorelOSContinuumConstruction D).toMeasurePackage.ready := by
  exact euclidean_yang_mills_projective_limit_rebase_ready D
    (finite_wilson_single_source_standardBorelLimit_eq_explicitLimit R)

/-- The compact-tightness route inherits the same four OS properties and is
ready for the OS/Wightman bridge. -/
theorem finite_wilson_single_source_compactTight_os_ready
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.compactTightOSContinuumConstruction D).toMeasurePackage.ready := by
  exact euclidean_yang_mills_projective_limit_rebase_ready D
    (finite_wilson_single_source_compactTightLimit_eq_explicitLimit R)

/-- Explicit common-source, standard-Borel, and compact-tightness constructions
are simultaneously ready for OS/Wightman reconstruction. -/
theorem finite_wilson_single_source_three_os_routes_ready
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction D).toMeasurePackage.ready :=
  ⟨finite_wilson_single_source_explicit_os_ready R D,
    finite_wilson_single_source_standardBorel_os_ready R D,
    finite_wilson_single_source_compactTight_os_ready R D⟩

/-- Every theorem-generated OS construction uses exactly the explicit
`globalObserve` pushforward Wilson law. -/
theorem finite_wilson_single_source_three_os_route_measures_eq_explicit
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure :=
  ⟨rfl,
    finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R,
    finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R⟩

/-- The standard-Borel and compact-tightness analytic constructions have the
same continuum law. -/
theorem finite_wilson_single_source_os_route_measures_agree
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_routes_agree R

end

end MathlibAnalytic
end MGAP4D
