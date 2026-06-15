import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Focused compile gate for the finite-discrete standard-Borel instance. -/
theorem finiteDiscrete_fieldValue_standardBorel_compile_smoke
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) :=
  finite_wilson_single_source_fieldValue_standardBorel R x

/-- Focused compile gate for finite-dimensional compact inner regularity. -/
theorem finiteDiscrete_innerRegular_compile_smoke
    (J : Finset EuclideanFourSpace) :
    (R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J).InnerRegularWRT
      (fun s => IsCompact s ∧ IsClosed s) MeasurableSet :=
  finite_wilson_single_source_finiteMarginal_innerRegular R J

/-- Focused compile gate for the bundled Standard-Borel projective limit. -/
noncomputable def finiteDiscrete_standardBorel_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteStandardBorelLimit

/-- Focused compile gate for the bundled compact-tightness projective limit. -/
noncomputable def finiteDiscrete_compactTight_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteCompactTightLimit

/-- Both constructions agree with the explicit Wilson pushforward. -/
theorem finiteDiscrete_routes_agree_compile_smoke :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.finiteDiscreteCompactTightLimit.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_routes_agree R

end

end MathlibAnalytic
end MGAP4D
