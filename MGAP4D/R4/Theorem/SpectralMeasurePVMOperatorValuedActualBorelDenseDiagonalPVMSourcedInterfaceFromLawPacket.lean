import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedLawPacketProof

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Rebuild a generic law-carrying spectral-measure interface from a dense-diagonal
PVM-sourced law packet. -/
def spectralMeasurePVMActualBorelGenericInterfaceOfDenseDiagonalPVMSourcedLawPacket
    (P : SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket) :
    SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface where
  map := P.actual_borel_map
  empty_maps_to_zero := P.empty_law
  univ_maps_to_identity := P.univ_law
  countable_additive := P.countable_additivity_law

/-- The generic law-carrying interface rebuilt from the current dense-diagonal
PVM-sourced law packet. -/
def spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacket :
    SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface :=
  spectralMeasurePVMActualBorelGenericInterfaceOfDenseDiagonalPVMSourcedLawPacket
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket

/-- The rebuilt dense-diagonal PVM-sourced generic interface has the same map as
the law packet. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_generic_interface_from_law_packet_map_eq :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacket.map =
      spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map := by
  rfl

/-- The rebuilt dense-diagonal PVM-sourced generic interface closes the generic
law-carrying residual target. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_generic_interface_from_law_packet_residual_closure :
    SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
      spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacket := by
  exact spectral_measure_pvm_actual_borel_generic_law_carrying_residual_closure_target
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacket

/-- The rebuilt dense-diagonal PVM-sourced generic interface keeps the PVM input
handoff attached. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacketReady : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacketReady ∧
  SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacket ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The rebuilt dense-diagonal PVM-sourced generic interface is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_generic_interface_from_law_packet_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedGenericInterfaceFromLawPacketReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_ready,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_generic_interface_from_law_packet_residual_closure,
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.pvm_input_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
