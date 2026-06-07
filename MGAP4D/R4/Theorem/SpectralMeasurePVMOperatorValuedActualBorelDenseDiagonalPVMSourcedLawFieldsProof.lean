import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The current dense-diagonal PVM-sourced law-carrying interface has the empty-set
law. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_empty_maps_to_zero :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.law_carrying_interface.map
        spectralMeasurePVMActualBorelEmptySet = 0 := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
    |>.law_carrying_interface
    |>.empty_maps_to_zero

/-- The current dense-diagonal PVM-sourced law-carrying interface has the univ-set
law. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_univ_maps_to_identity :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.law_carrying_interface.map
        spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MGAP4D.MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
    |>.law_carrying_interface
    |>.univ_maps_to_identity

/-- The current dense-diagonal PVM-sourced law-carrying interface has countable
additivity on actual-Borel carrier families. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_countable_additive :
    ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
      SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
        spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
            (fun n : ℕ =>
              spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
                |>.law_carrying_interface
                |>.map (F n)) =
          spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
            |>.law_carrying_interface
            |>.map (spectralMeasurePVMActualBorelCarrierSetIUnion F) := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
    |>.law_carrying_interface
    |>.countable_additive

/-- The current dense-diagonal PVM-sourced law-carrying interface closes the
generic law-carrying residual target. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_residual_closure :
    SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
      spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.law_carrying_interface := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.residual_closure

/-- The dense-diagonal PVM input handoff is explicitly attached to the current
law-carrying interface. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_input_handoff_ready :
    MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.pvm_input_ready

/-- Combined law-field proof packet for the current dense-diagonal PVM-sourced
law-carrying interface. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawFieldsProofReady : Prop :=
  spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.law_carrying_interface.map
      spectralMeasurePVMActualBorelEmptySet = 0 ∧
  spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.law_carrying_interface.map
      spectralMeasurePVMActualBorelUnivSet =
    ContinuousLinearMap.id ℝ MGAP4D.MathlibAnalytic.ConcreteL2R1HilbertCarrier ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
          (fun n : ℕ =>
            spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
              |>.law_carrying_interface
              |>.map (F n)) =
        spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent
          |>.law_carrying_interface
          |>.map (spectralMeasurePVMActualBorelCarrierSetIUnion F)) ∧
  SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawCarryingInterfaceCurrent.law_carrying_interface ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The combined law-field proof packet is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_fields_proof_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawFieldsProofReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_empty_maps_to_zero,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_univ_maps_to_identity,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_countable_additive,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_residual_closure,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_input_handoff_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
