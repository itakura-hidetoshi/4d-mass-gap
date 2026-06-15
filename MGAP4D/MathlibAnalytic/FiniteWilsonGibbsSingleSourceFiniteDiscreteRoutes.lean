import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitThreeRoutes
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Every finite discrete Wilson field-value carrier is standard Borel. -/
theorem finite_wilson_single_source_fieldValue_standardBorel
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) := by
  infer_instance

/-- The coordinatewise standard-Borel instance family. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.fieldValueStandardBorelFamily :
    ∀ x, StandardBorelSpace (R.fieldValue x) :=
  fun x => finite_wilson_single_source_fieldValue_standardBorel R x

/-- Use the literal discrete topology on each finite Wilson field-value carrier. -/
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

/-- The finite dependent-product carrier has a finite enumeration. -/
noncomputable def finite_wilson_single_source_finiteProduct_fintype
    (J : Finset EuclideanFourSpace) :
    Fintype (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- Every subset of a finite-dimensional Wilson carrier is finite. -/
theorem finite_wilson_single_source_finiteProduct_set_finite
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    A.Finite := by
  letI : Fintype (∀ x : J, R.fieldValue x) :=
    finite_wilson_single_source_finiteProduct_fintype R J
  exact Set.toFinite A

/-- Every subset of a finite-dimensional Wilson carrier is compact. -/
theorem finite_wilson_single_source_finiteProduct_set_compact
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    IsCompact A :=
  (finite_wilson_single_source_finiteProduct_set_finite R J A).isCompact

/-- Every subset of a finite-dimensional Wilson carrier is closed. -/
theorem finite_wilson_single_source_finiteProduct_set_closed
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    IsClosed A :=
  (finite_wilson_single_source_finiteProduct_set_finite R J A).isClosed

/-- Every finite-dimensional Wilson marginal is compact inner regular. -/
theorem finite_wilson_single_source_finiteMarginal_innerRegular
    (J : Finset EuclideanFourSpace) :
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J).InnerRegularWRT
      (fun s => IsCompact s ∧ IsClosed s) MeasurableSet := by
  letI : IsProbabilityMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) :=
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginalProbability J
  exact innerRegular_isCompact_isClosed_measurableSet_of_finite
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J)

/-- Standard-Borel projective limit generated from finite discrete Wilson field
values. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteStandardBorelLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  @euclideanYangMillsStandardBorelProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.fieldValueStandardBorelFamily

/-- The Standard-Borel construction is exactly the explicit common-source
pushforward continuum law. -/
theorem finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteStandardBorelLimit.continuumMeasure
    R.finiteDiscreteStandardBorelLimit.projectiveLimit

end

end MathlibAnalytic
end MGAP4D
