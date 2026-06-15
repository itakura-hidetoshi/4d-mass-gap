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

/-- The full coordinatewise standard-Borel instance family. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.fieldValueStandardBorelFamily :
    ∀ x, StandardBorelSpace (R.fieldValue x) :=
  fun x => finite_wilson_single_source_fieldValue_standardBorel R x

/-- Use the literal discrete topology on every finite Wilson field-value carrier. -/
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

/-- The finite dependent product topology is discrete. -/
theorem finite_wilson_single_source_finiteProduct_discrete
    (J : Finset EuclideanFourSpace) :
    DiscreteTopology (∀ x : J, R.fieldValue x) := by
  infer_instance

/-- Every finite-dimensional Wilson marginal is compact inner regular.  Since
its carrier is finite, a measurable set is itself a finite compact closed inner
approximation, with no probability loss. -/
theorem finite_wilson_single_source_finiteMarginal_innerRegular
    (J : Finset EuclideanFourSpace) :
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J).InnerRegularWRT
      (fun s => IsCompact s ∧ IsClosed s) MeasurableSet := by
  classical
  letI : DiscreteTopology (∀ x : J, R.fieldValue x) :=
    finite_wilson_single_source_finiteProduct_discrete R J
  intro A hA r hr
  have hAfin : A.Finite := Set.toFinite A
  exact ⟨A, subset_rfl, ⟨hAfin.isCompact, hAfin.isClosed⟩, hr.le⟩

/-- Standard-Borel projective limit generated automatically from finite
discrete Wilson field values. -/
noncomputable def
    FiniteWilsonGibbsSingleSourceProjectiveRealization.finiteDiscreteStandardBorelLimit :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  @euclideanYangMillsStandardBorelProjectiveLimitMeasure
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.fieldValueStandardBorelFamily

/-- The finite-discrete Standard-Borel construction is exactly the explicit
common-source pushforward continuum law. -/
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

/-- The compact-tightness construction is the explicit Wilson pushforward law. -/
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
