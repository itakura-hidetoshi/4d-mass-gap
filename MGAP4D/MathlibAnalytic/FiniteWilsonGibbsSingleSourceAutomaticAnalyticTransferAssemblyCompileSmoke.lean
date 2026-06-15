import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceAutomaticAnalyticTransferAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

variable
  (C : FiniteWilsonGibbsSingleSourceRemainingOSAnalyticTransferData R)
  (D : FiniteWilsonOSAutomaticReflectionLimitData W)

/-- Compile gate for completing the generic transfer package with the concrete
finite-Wilson reflection sequence. -/
noncomputable def finite_wilson_automatic_analytic_transfer_compile_smoke :
    FiniteWilsonGibbsSingleSourceOSPropertyTransferData R :=
  R.osAnalyticTransferDataOfAutomaticReflection C D

/-- Compile gate for definitional identification of the inserted reflection
component. -/
theorem finite_wilson_automatic_reflection_component_compile_smoke :
    (R.osAnalyticTransferDataOfAutomaticReflection C D).reflectionLimit =
      D.toReflectionPositivityLimitData :=
  finite_wilson_single_source_automatic_transfer_reflectionLimit R C D

/-- Compile gate for theorem-generated continuum reflection positivity inside
the completed analytic transfer record. -/
theorem finite_wilson_automatic_reflection_positive_compile_smoke :
    (R.osAnalyticTransferDataOfAutomaticReflection C D).reflectionLimit.ContinuumReflectionPositive :=
  C.automaticWilsonReflectionPositive D

/-- Compile gate for the explicit route after automatic reflection assembly. -/
theorem finite_wilson_explicit_ready_of_automatic_reflection_compile_smoke :
    (R.explicitOSContinuumConstruction
      (R.osAnalyticTransferDataOfAutomaticReflection C D)).toMeasurePackage.ready :=
  finite_wilson_single_source_explicit_os_ready_of_automatic_reflection R C D

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

variable
  (S : EuclideanYangMillsCountableSkeletonData
    R.toProjectiveRealization.toProjectiveCylinderFamily κ β)

/-- Compile gate for simultaneous four-route readiness with automatic finite
Wilson reflection positivity. -/
theorem finite_wilson_four_routes_ready_of_automatic_reflection_compile_smoke :
    (R.explicitOSContinuumConstruction
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).toMeasurePackage.ready :=
  finite_wilson_single_source_four_os_routes_ready_of_automatic_reflection
    R S C D

/-- Compile gate for equality of all automatically assembled continuum laws. -/
theorem finite_wilson_four_route_measures_of_automatic_reflection_compile_smoke :
    (R.explicitOSContinuumConstruction
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.osAnalyticTransferDataOfAutomaticReflection C D)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_four_os_route_measures_eq_explicit_of_automatic_reflection
    R S C D

end

end MathlibAnalytic
end MGAP4D
