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

/-- Every finite-dimensional Wilson marginal is compact inner regular. The
measurable set itself is the compact closed inner approximation, with no loss. -/
theorem finite_wilson_single_source_finiteMarginal_innerRegular
    (J : Finset EuclideanFourSpace) :
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J).InnerRegularWRT
      (fun s => IsCompact s ∧ IsClosed s) MeasurableSet := by
  intro A hA r hr
  exact ⟨A, subset_rfl,
    ⟨finite_wilson_single_source_finiteProduct_set_compact R J A,
      finite_wilson_single_source_finiteProduct_set_closed R J A⟩,
    hr⟩

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

/-- Compact-tightness data obtained directly from finiteness of every marginal
configuration carrier. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteCompactTightnessData :
    EuclideanYangMillsCompactTightnessData
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  { innerRegular := finite_wilson_single_source_finiteMarginal_innerRegular R }

/-- Compact-tightness projective limit generated from finite discrete Wilson
marginals. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteCompactTightLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  euclideanYangMillsCompactTightProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.finiteDiscreteCompactTightnessData

/-- The compact-tightness construction is the explicit common-source law. -/
theorem finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit :
    R.finiteDiscreteCompactTightLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    R.finiteDiscreteCompactTightLimit.continuumMeasure
    R.finiteDiscreteCompactTightLimit.projectiveLimit

/-- The Standard-Borel and compact-tightness constructions agree exactly. -/
theorem finite_wilson_single_source_finiteDiscrete_routes_agree :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.finiteDiscreteCompactTightLimit.continuumMeasure := by
  rw [finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R,
    finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R]

end

end MathlibAnalytic
end MGAP4D
