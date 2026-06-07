import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedLawFieldsProof

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Law packet for the dense-diagonal PVM-sourced actual-Borel map. -/
structure SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket where
  actual_borel_map : SpectralMeasurePVMActualBorelCarrierSet → SpectralMeasurePVMActualBorelProjectionOperator
  empty_law : actual_borel_map spectralMeasurePVMActualBorelEmptySet = 0
  univ_law :
    actual_borel_map spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MGAP4D.MathlibAnalytic.ConcreteL2R1HilbertCarrier
  countable_additivity_law :
    ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
      SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
        spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
            (fun n : ℕ => actual_borel_map (F n)) =
          actual_borel_map (spectralMeasurePVMActualBorelCarrierSetIUnion F)
  residual_closure :
    SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
      spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedCurrentInterface
  pvm_input_ready :
    MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady
  no_shell_to_full_collapse_boundary : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The dense-diagonal PVM-sourced actual-Borel law packet. -/
def spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket where
  actual_borel_map := spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedCurrentMap
  empty_law :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_empty_maps_to_zero
  univ_law :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_univ_maps_to_identity
  countable_additivity_law :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_countable_additive
  residual_closure :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_residual_closure
  pvm_input_ready :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_current_input_handoff_ready
  no_shell_to_full_collapse_boundary :=
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- The law packet exposes the actual-Borel empty-set law. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_empty_law :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map
        spectralMeasurePVMActualBorelEmptySet = 0 := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.empty_law

/-- The law packet exposes the actual-Borel univ-set law. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_univ_law :
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map
        spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MGAP4D.MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.univ_law

/-- The law packet exposes actual-Borel countable additivity. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_countable_additivity :
    ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
      SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
        spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
            (fun n : ℕ =>
              spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map (F n)) =
          spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map
            (spectralMeasurePVMActualBorelCarrierSetIUnion F) := by
  exact spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.countable_additivity_law

/-- The dense-diagonal PVM-sourced law packet is ready. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacketReady : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawFieldsProofReady ∧
  spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map
      spectralMeasurePVMActualBorelEmptySet = 0 ∧
  spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.actual_borel_map
      spectralMeasurePVMActualBorelUnivSet =
    ContinuousLinearMap.id ℝ MGAP4D.MathlibAnalytic.ConcreteL2R1HilbertCarrier ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The dense-diagonal PVM-sourced law packet is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacketReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_fields_proof_ready,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_empty_law,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_law_packet_univ_law,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
