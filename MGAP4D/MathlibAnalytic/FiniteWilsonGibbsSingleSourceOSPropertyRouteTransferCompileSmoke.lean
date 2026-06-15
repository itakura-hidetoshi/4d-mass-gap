import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceOSPropertyRouteTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Compile gate for the standard-Borel route equality. -/
theorem finite_wilson_standardBorel_os_transfer_compile_smoke :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure :=
  finite_wilson_single_source_standardBorelLimit_eq_explicitLimit R

/-- Compile gate for the compact-tightness route equality. -/
theorem finite_wilson_compactTight_os_transfer_compile_smoke :
    R.finiteDiscreteCompactTightLimit.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure :=
  finite_wilson_single_source_compactTightLimit_eq_explicitLimit R

/-- Compile gate for readiness of the explicit common-source route. -/
theorem finite_wilson_explicit_os_ready_compile_smoke
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).toMeasurePackage.ready :=
  finite_wilson_single_source_explicit_os_ready R D

/-- Compile gate for readiness of the standard-Borel route. -/
theorem finite_wilson_standardBorel_os_ready_compile_smoke
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.standardBorelOSContinuumConstruction D).toMeasurePackage.ready :=
  finite_wilson_single_source_standardBorel_os_ready R D

/-- Compile gate for readiness of the compact-tightness route. -/
theorem finite_wilson_compactTight_os_ready_compile_smoke
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.compactTightOSContinuumConstruction D).toMeasurePackage.ready :=
  finite_wilson_single_source_compactTight_os_ready R D

/-- Compile gate for simultaneous readiness of all three closed routes. -/
theorem finite_wilson_three_os_routes_ready_compile_smoke
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction D).toMeasurePackage.ready :=
  finite_wilson_single_source_three_os_routes_ready R D

/-- Compile gate showing that all three constructions use the explicit
`globalObserve` pushforward law. -/
theorem finite_wilson_three_os_route_measures_eq_explicit_compile_smoke
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.explicitOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_three_os_route_measures_eq_explicit R D

/-- Compile gate for agreement of the standard-Borel and compact-tightness
analytic constructions. -/
theorem finite_wilson_os_route_measures_agree_compile_smoke
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure :=
  finite_wilson_single_source_os_route_measures_agree R D

end

end MathlibAnalytic
end MGAP4D
