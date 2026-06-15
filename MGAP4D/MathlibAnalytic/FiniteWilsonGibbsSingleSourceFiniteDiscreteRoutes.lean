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

/-- Bridge the concrete Wilson field topology across the projective-family
record projections. -/
local instance finiteDiscreteProjectiveFieldValueTopologicalSpace
    (x : EuclideanFourSpace) :
    TopologicalSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) := by
  change TopologicalSpace (R.fieldValue x)
  infer_instance

local instance finiteDiscreteProjectiveFieldValueOpensMeasurableSpace
    (x : EuclideanFourSpace) :
    OpensMeasurableSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) := by
  change OpensMeasurableSpace (R.fieldValue x)
  infer_instance

local instance finiteDiscreteProjectiveFieldValueSecondCountableTopology
    (x : EuclideanFourSpace) :
    SecondCountableTopology
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) := by
  change SecondCountableTopology (R.fieldValue x)
  infer_instance

local instance finiteDiscreteFiniteProductTopologicalSpace
    (J : Finset EuclideanFourSpace) :
    TopologicalSpace (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- The projective-family field projection is definitionally the original
Wilson field family, but instance search does not unfold that record path. -/
local instance finiteDiscreteProjectiveFiniteProductTopologicalSpace
    (J : Finset EuclideanFourSpace) :
    TopologicalSpace
      (∀ x : J,
        R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) := by
  change TopologicalSpace (∀ x : J, R.fieldValue x)
  infer_instance

local instance finiteDiscreteProjectiveFiniteProductBorelSpace
    (J : Finset EuclideanFourSpace) :
    BorelSpace
      (∀ x : J,
        R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) := by
  change BorelSpace (∀ x : J, R.fieldValue x)
  infer_instance

local instance finiteDiscreteProjectiveFiniteProductPolishSpace
    (J : Finset EuclideanFourSpace) :
    PolishSpace
      (∀ x : J,
        R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) := by
  change PolishSpace (∀ x : J, R.fieldValue x)
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
  letI : IsFiniteMeasure
      (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J) :=
    finite_wilson_single_source_finiteMarginal_isFinite R J
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

/-- Compact-tightness data obtained directly from finite-dimensional inner
regularity. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteCompactTightnessData :
    EuclideanYangMillsCompactTightnessData
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  { innerRegular := finite_wilson_single_source_finiteMarginal_innerRegular R }

/-- Compact-tightness projective limit generated from the same finite Wilson
marginals. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteCompactTightLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  euclideanYangMillsCompactTightProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.finiteDiscreteCompactTightnessData

/-- The compact-tightness construction is exactly the explicit common-source
pushforward continuum law. -/
theorem finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit :
    R.finiteDiscreteCompactTightLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteCompactTightLimit.continuumMeasure
    R.finiteDiscreteCompactTightLimit.projectiveLimit

/-- The Standard-Borel and compact-tightness continuum constructions coincide. -/
theorem finite_wilson_single_source_finiteDiscrete_routes_agree :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.finiteDiscreteCompactTightLimit.continuumMeasure := by
  rw [finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R,
    finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R]

end

end MathlibAnalytic
end MGAP4D
