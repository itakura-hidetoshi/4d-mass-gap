import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteOSPropertyTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

variable
  (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure)

/-- Focused compile gate for Standard-Borel analytic-data transport. -/
noncomputable def finiteDiscrete_standardBorel_os_transfer_compile_smoke :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.finiteDiscreteStandardBorelLimit :=
  finite_wilson_single_source_finiteDiscrete_standardBorel_analyticTransferData R D

/-- Focused compile gate for compact-tightness analytic-data transport. -/
noncomputable def finiteDiscrete_compactTight_os_transfer_compile_smoke :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.finiteDiscreteCompactTightLimit :=
  finite_wilson_single_source_finiteDiscrete_compactTight_analyticTransferData R D

/-- The Standard-Borel route remains OS/Wightman ready. -/
theorem finiteDiscrete_standardBorel_os_transfer_ready_compile_smoke :
    (finiteDiscrete_standardBorel_os_transfer_compile_smoke R D)
      .toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_single_source_finiteDiscrete_standardBorel_transfer_ready R D

/-- The compact-tightness route remains OS/Wightman ready. -/
theorem finiteDiscrete_compactTight_os_transfer_ready_compile_smoke :
    (finiteDiscrete_compactTight_os_transfer_compile_smoke R D)
      .toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_single_source_finiteDiscrete_compactTight_transfer_ready R D

/-- All three continuum constructions are simultaneously OS/Wightman ready. -/
theorem finiteDiscrete_three_route_os_transfer_ready_compile_smoke :
    D.toContinuumConstruction.toMeasurePackage.ready ∧
      (finiteDiscrete_standardBorel_os_transfer_compile_smoke R D)
        .toContinuumConstruction.toMeasurePackage.ready ∧
      (finiteDiscrete_compactTight_os_transfer_compile_smoke R D)
        .toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_single_source_finiteDiscrete_three_route_transfer_ready R D

/-- All three theorem-generated analytic constructions use the explicit
`globalObserve` pushforward law. -/
theorem finiteDiscrete_three_route_os_transfer_measures_compile_smoke :
    D.toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finiteDiscrete_standardBorel_os_transfer_compile_smoke R D)
          .toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure ∧
      (finiteDiscrete_compactTight_os_transfer_compile_smoke R D)
          .toContinuumConstruction.limit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_three_route_transfer_measures R D

end

end MathlibAnalytic
end MGAP4D
