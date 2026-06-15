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

/-- Focused compile gate for finite dependent-product enumeration. -/
noncomputable def finiteDiscrete_finiteProduct_fintype_compile_smoke
    (J : Finset EuclideanFourSpace) :
    Fintype (∀ x : J, R.fieldValue x) :=
  finite_wilson_single_source_finiteProduct_fintype R J

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

/-- The Standard-Borel law agrees with the explicit Wilson pushforward. -/
theorem finiteDiscrete_standardBorel_eq_explicit_compile_smoke :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_standardBorel_eq_explicit R

end

end MathlibAnalytic
end MGAP4D
