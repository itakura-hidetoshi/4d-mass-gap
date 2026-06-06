import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSigmaAlgebraCarrierCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Phase surface for the actual-Borel sigma-algebra style carrier certificate.

This phase is intentionally carrier-side only.  It packages the wrapper
existence, endpoint lifting, Boolean closure, countable union closure, and
countable intersection closure before the projection-valued map interface.  It
keeps the genuine operator-topology and spectral-theorem boundaries open. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraCarrierCertificatePhaseSurfaceReady : Prop :=
  SpectralMeasurePVMActualBorelSigmaAlgebraCarrierCertificatePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSigmaAlgebraCarrierCertificateTarget ∧
  SpectralMeasurePVMActualBorelMeasurableSetClosurePackagePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetWrapperBooleanClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableUnionClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableInterClosureTarget ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel sigma-algebra style carrier certificate phase surface is ready. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_carrier_certificate_phase_surface_ready :
    SpectralMeasurePVMActualBorelSigmaAlgebraCarrierCertificatePhaseSurfaceReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_sigma_algebra_carrier_certificate_public_boundary_held,
    spectral_measure_pvm_actual_borel_sigma_algebra_carrier_certificate_target_ready,
    spectral_measure_pvm_actual_borel_measurable_set_closure_package_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_wrapper_boolean_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_union_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
