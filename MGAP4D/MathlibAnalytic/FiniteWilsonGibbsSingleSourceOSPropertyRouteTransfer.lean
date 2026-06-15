import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransferRebase
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCountableSkeletonExtension

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

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

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- Any countable-skeleton reconstruction of the same Wilson finite marginals
is equal to the explicit common-source continuum law. -/
theorem finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β) :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure := by
  change S.continuumMeasure = R.continuumMeasure
  exact finite_wilson_gibbs_single_source_constructed_unique R
    S.continuumMeasure S.isProjectiveLimit

/-- Rebase all four transferred OS properties to an arbitrary countable
standard-Borel skeleton reconstruction recovering the Wilson finite laws. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.countableSkeletonOSContinuumConstruction
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  (D.rebaseLimit
    (finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S)).toContinuumConstruction

/-- The countable-skeleton route inherits the same four OS properties and is
ready for the OS/Wightman bridge. -/
theorem finite_wilson_single_source_countableSkeleton_os_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.countableSkeletonOSContinuumConstruction S D).toMeasurePackage.ready := by
  exact euclidean_yang_mills_projective_limit_rebase_ready D
    (finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S)

/-- All three independent existence routes carry exactly the same continuum
law as the explicit common-source route. -/
theorem finite_wilson_single_source_os_route_measures_agree
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
        (R.compactTightOSContinuumConstruction D).limit.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure =
        (R.countableSkeletonOSContinuumConstruction S D).limit.continuumMeasure := by
  constructor
  · exact finite_wilson_single_source_finiteDiscrete_routes_agree R
  · rw [finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R]
    exact (finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S).symm

end

end MathlibAnalytic
end MGAP4D
