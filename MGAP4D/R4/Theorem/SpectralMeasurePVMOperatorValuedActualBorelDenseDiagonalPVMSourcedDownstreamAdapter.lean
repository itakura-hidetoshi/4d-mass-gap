import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedInterfaceFromLawPacket

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Dense-diagonal PVM-sourced replacement for downstream uses of the generic
law-carrying actual-Borel interface. -/
def spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface :
    SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface :=
  spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacket

/-- The downstream dense-diagonal PVM-sourced interface closes the generic
law-carrying residual target. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_interface_residual_closure :
    SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
      spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface := by
  exact spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_generic_interface_from_law_packet_residual_closure

/-- The downstream dense-diagonal PVM-sourced interface has the empty-set law. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_interface_empty_law :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.map
        spectralMeasurePVMActualBorelEmptySet = 0 := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.empty_maps_to_zero

/-- The downstream dense-diagonal PVM-sourced interface has the univ-set law. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_interface_univ_law :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.map
        spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MGAP4D.MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.univ_maps_to_identity

/-- The downstream dense-diagonal PVM-sourced interface has countable additivity. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_interface_countable_additivity :
    ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
      SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
        spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
            (fun n : ℕ =>
              spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.map (F n)) =
          spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.map
            (spectralMeasurePVMActualBorelCarrierSetIUnion F) := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface.countable_additive

/-- The downstream adapter carries the dense diagonal PVM input handoff. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamAdapterReady : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacketReady ∧
  SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The downstream adapter for the dense-diagonal PVM-sourced interface is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_adapter_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamAdapterReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_generic_interface_from_law_packet_ready,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_interface_residual_closure,
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.pvm_input_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
