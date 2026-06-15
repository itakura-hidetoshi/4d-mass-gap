import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

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

/-- The Standard-Borel law agrees with the explicit common-source law. -/
theorem finiteDiscrete_standardBorel_eq_explicit_compile_smoke :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R

/-- The compact-tightness law agrees with the explicit common-source law. -/
theorem finiteDiscrete_compactTight_eq_explicit_compile_smoke :
    R.finiteDiscreteCompactTightLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_compactTight_eq_explicit R

/-- Both independently constructed continuum measures agree exactly. -/
theorem finiteDiscrete_routes_agree_compile_smoke :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.finiteDiscreteCompactTightLimit.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_routes_agree R

end

end MathlibAnalytic
end MGAP4D
