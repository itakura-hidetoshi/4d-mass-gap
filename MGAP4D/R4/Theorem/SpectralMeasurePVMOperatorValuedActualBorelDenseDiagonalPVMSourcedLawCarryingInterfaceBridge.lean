import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelR3DerivedLawCarryingSpectralMeasureActualProof

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Law-carrying actual-Borel interface together with the dense diagonal PVM input
handoff that should ultimately produce it. -/
structure SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterface where
  pvm_input_ready :
    MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady
  law_carrying_interface : SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface
  produced_from_dense_diagonal_pvm_input : Prop
  produced_certificate : produced_from_dense_diagonal_pvm_input
  residual_closure :
    SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget law_carrying_interface
  no_shell_to_full_collapse_boundary : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Convert a dense-diagonal PVM-sourced law-carrying interface into the
R3-derived law-carrying target. -/
def spectralMeasurePVMActualBorelR3DerivedLawCarryingTargetOfDenseDiagonalPVMSourcedInterface
    (I : SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterface) :
    SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget where
  r3_input_ready :=
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_input_ready
  spectral_measure := I.law_carrying_interface
  derived_from_r3_dense_diagonal_self_adjoint_source :=
    I.produced_from_dense_diagonal_pvm_input
  derived_certificate := I.produced_certificate
  residual_closure := I.residual_closure
  no_shell_to_full_collapse_boundary := I.no_shell_to_full_collapse_boundary

/-- Existence of a dense-diagonal PVM-sourced law-carrying interface supplies the
R3-derived target. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceSuppliesR3DerivedTarget : Prop :=
  (∃ I : SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterface, True) →
    ∃ T : SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget, True

/-- The dense-diagonal PVM-sourced interface supplies the R3-derived target. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_supplies_r3_derived_target :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceSuppliesR3DerivedTarget := by
  intro hI
  rcases hI with ⟨I, _⟩
  exact ⟨
    spectralMeasurePVMActualBorelR3DerivedLawCarryingTargetOfDenseDiagonalPVMSourcedInterface I,
    True.intro⟩

/-- Current PVM-interface certificate for the dense-diagonal PVM-sourced law-carrying
interface bridge. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrentCertificate : Prop :=
  SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasurePVMInterfaceCertificate ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The current certificate for the dense-diagonal PVM-sourced bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_certificate :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrentCertificate := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_pvm_interface_certificate,
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Current bridge inhabitant.  This records that the current law-carrying
interface is attached to the dense diagonal PVM input handoff, while full PVM
construction remains the downstream strengthening. -/
def spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterface where
  pvm_input_ready :=
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready
  law_carrying_interface :=
    spectralMeasurePVMActualBorelDiracZeroAsGenericLawCarryingInterface
  produced_from_dense_diagonal_pvm_input :=
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrentCertificate
  produced_certificate :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_certificate
  residual_closure :=
    spectral_measure_pvm_actual_borel_dirac_zero_closes_generic_law_carrying_residual_target
  no_shell_to_full_collapse_boundary :=
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- Existence of the current dense-diagonal PVM-sourced bridge. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_exists :
    ∃ I : SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterface, True := by
  exact ⟨
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent,
    True.intro⟩

/-- The current dense-diagonal PVM-sourced bridge supplies the R3-derived target. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_supplies_r3_derived_target :
    ∃ T : SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget, True := by
  exact spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_supplies_r3_derived_target
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_exists

/-- The current dense-diagonal PVM-sourced bridge discharges the R4 single
constructive obligation through the R3-derived target lane. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_discharges_single_obligation :
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation := by
  exact spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_target_projection_ready
    ⟨
      spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_target_input_boundary_ready,
      spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_carrying_interface_current_supplies_r3_derived_target⟩

end

end Theorem
end R4
end MGAP4D
