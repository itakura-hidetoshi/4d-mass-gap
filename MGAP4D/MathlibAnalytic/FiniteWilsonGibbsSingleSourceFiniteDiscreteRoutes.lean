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

local instance finiteDiscreteFieldValueTopologicalSpace
    (x : EuclideanFourSpace) : TopologicalSpace (R.fieldValue x) :=
  ⊥

local instance finiteDiscreteFieldValueDiscreteTopology
    (x : EuclideanFourSpace) : DiscreteTopology (R.fieldValue x) :=
  ⟨rfl⟩

local instance finiteDiscreteFieldValueBorelSpace
    (x : EuclideanFourSpace) : BorelSpace (R.fieldValue x) := by
  infer_instance

local instance finiteDiscreteFieldValuePolishSpace
    (x : EuclideanFourSpace) : PolishSpace (R.fieldValue x) := by
  infer_instance

/-- The finite dependent product carries the expected Borel structure. -/
theorem finite_wilson_single_source_finiteProduct_borel
    (J : Finset EuclideanFourSpace) :
    BorelSpace (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- The finite dependent product is second countable. -/
theorem finite_wilson_single_source_finiteProduct_secondCountable
    (J : Finset EuclideanFourSpace) :
    SecondCountableTopology (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- The finite dependent product topology is discrete. -/
theorem finite_wilson_single_source_finiteProduct_discrete
    (J : Finset EuclideanFourSpace) :
    DiscreteTopology (∀ x : J, R.fieldValue x) := by
  infer_instance

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

end

end MathlibAnalytic
end MGAP4D
