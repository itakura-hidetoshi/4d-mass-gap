import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitThreeRoutes
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Every countable discrete Wilson field-value carrier is standard Borel. -/
theorem finite_wilson_single_source_fieldValue_standardBorel
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) := by
  infer_instance

/-- The full coordinatewise standard-Borel instance family. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.fieldValueStandardBorelFamily :
    ∀ x, StandardBorelSpace (R.fieldValue x) :=
  fun x => finite_wilson_single_source_fieldValue_standardBorel R x

/-- Standard-Borel projective limit generated automatically from countable
discrete Wilson field values. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteStandardBorelLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  @euclideanYangMillsStandardBorelProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.fieldValueStandardBorelFamily

/-- The countable-discrete Standard-Borel construction is exactly the explicit
common-source pushforward continuum law. -/
theorem finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteStandardBorelLimit.continuumMeasure
    R.finiteDiscreteStandardBorelLimit.projectiveLimit

/-- Compact-inner-regularity is automatic after equipping each countable
discrete coordinate with its compatible upgraded Polish topology. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteCompactTightLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily := by
  letI : ∀ x, StandardBorelSpace (R.fieldValue x) :=
    R.fieldValueStandardBorelFamily
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

end

end MathlibAnalytic
end MGAP4D
