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

theorem finite_wilson_single_source_fieldValue_standardBorel
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) := by
  infer_instance

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

/-- Install the product topology before statements mentioning compact or closed
subsets of a finite Wilson carrier are elaborated. -/
local instance finiteDiscreteFiniteProductTopologicalSpace
    (J : Finset EuclideanFourSpace) :
    TopologicalSpace (∀ x : J, R.fieldValue x) := by
  infer_instance

noncomputable def finite_wilson_single_source_finiteProduct_fintype
    (J : Finset EuclideanFourSpace) :
    Fintype (∀ x : J, R.fieldValue x) := by
  infer_instance

theorem finite_wilson_single_source_finiteProduct_set_finite
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    A.Finite := by
  letI : Fintype (∀ x : J, R.fieldValue x) :=
    finite_wilson_single_source_finiteProduct_fintype R J
  exact Set.toFinite A

theorem finite_wilson_single_source_finiteProduct_set_compact
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    IsCompact A :=
  (finite_wilson_single_source_finiteProduct_set_finite R J A).isCompact

theorem finite_wilson_single_source_finiteProduct_set_closed
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    IsClosed A :=
  (finite_wilson_single_source_finiteProduct_set_finite R J A).isClosed

/-- Audit: each finite Wilson carrier has the expected Borel topology. -/
theorem finite_wilson_single_source_finiteProduct_borel
    (J : Finset EuclideanFourSpace) :
    BorelSpace (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- Audit: each finite Wilson carrier is Polish. -/
theorem finite_wilson_single_source_finiteProduct_polish
    (J : Finset EuclideanFourSpace) :
    PolishSpace (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- Audit: each Wilson finite marginal is a finite measure. -/
theorem finite_wilson_single_source_finiteMarginal_isFinite
    (J : Finset EuclideanFourSpace) :
    IsFiniteMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) := by
  letI : IsProbabilityMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) :=
    R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginalProbability J
  infer_instance

/-- Every Wilson finite marginal is compact inner regular. -/
theorem finite_wilson_single_source_finiteMarginal_innerRegular
    (J : Finset EuclideanFourSpace) :
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J).InnerRegularWRT
      (fun s => IsCompact s ∧ IsClosed s) MeasurableSet := by
  letI : BorelSpace (∀ x : J, R.fieldValue x) :=
    finite_wilson_single_source_finiteProduct_borel R J
  letI : PolishSpace (∀ x : J, R.fieldValue x) :=
    finite_wilson_single_source_finiteProduct_polish R J
  letI : IsFiniteMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) :=
    finite_wilson_single_source_finiteMarginal_isFinite R J
  exact innerRegular_isCompact_isClosed_measurableSet_of_finite
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J)

noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteStandardBorelLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  @euclideanYangMillsStandardBorelProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.fieldValueStandardBorelFamily

theorem finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteStandardBorelLimit.continuumMeasure
    R.finiteDiscreteStandardBorelLimit.projectiveLimit

end

end MathlibAnalytic
end MGAP4D
