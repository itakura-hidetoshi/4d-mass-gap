import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitThreeRoutes
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

section FiniteDiscreteSingleSource

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Every finite discrete Wilson field-value carrier is standard Borel. -/
theorem finite_wilson_single_source_fieldValue_standardBorel
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) := by
  infer_instance

/-- Standard-Borel projective limit generated automatically from finite discrete
Wilson field values. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteStandardBorelLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily := by
  letI : ∀ x, StandardBorelSpace (R.fieldValue x) :=
    fun x => finite_wilson_single_source_fieldValue_standardBorel R x
  exact euclideanYangMillsStandardBorelProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily

/-- The finite-discrete standard-Borel construction is the same continuum law
as the explicit common-source pushforward. -/
theorem finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteStandardBorelLimit.continuumMeasure
    R.finiteDiscreteStandardBorelLimit.projectiveLimit

/-- Compact-inner-regularity data are automatic after giving each finite
field-value carrier its compatible upgraded Polish topology. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteCompactTightLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily := by
  letI : ∀ x, StandardBorelSpace (R.fieldValue x) :=
    fun x => finite_wilson_single_source_fieldValue_standardBorel R x
  letI := fun x => upgradeStandardBorel (R.fieldValue x)
  letI : ∀ J,
      IsProbabilityMeasure
        (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) :=
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginalProbability
  let T : EuclideanYangMillsCompactTightnessData
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
    { innerRegular := fun J =>
        innerRegular_isCompact_isClosed_measurableSet_of_finite
          (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) }
  exact euclideanYangMillsCompactTightProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily T

/-- The finite-discrete compact-tightness construction is also the explicit
Wilson common-source continuum law. -/
theorem finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit :
    R.finiteDiscreteCompactTightLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteCompactTightLimit.continuumMeasure
    R.finiteDiscreteCompactTightLimit.projectiveLimit

/-- The standard-Borel and compact-tightness routes coincide exactly. -/
theorem finite_wilson_single_source_finiteDiscrete_routes_agree :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.finiteDiscreteCompactTightLimit.continuumMeasure := by
  rw [finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R,
    finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R]

end FiniteDiscreteSingleSource

end

end MathlibAnalytic
end MGAP4D
