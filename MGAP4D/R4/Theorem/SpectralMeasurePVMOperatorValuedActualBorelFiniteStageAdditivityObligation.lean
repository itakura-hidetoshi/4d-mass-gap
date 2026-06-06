import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelFiniteStageObligationPacket

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Finite-stage projection additivity law attached to a finite-stage obligation packet.

This is a finite-stage obligation, not a countable-additivity theorem.  It says
that the projection of the successor finite union equals the pointwise sum of
the projection of the previous finite union and the next set. -/
def SpectralMeasurePVMActualBorelFiniteStageProjectionAdditivityLaw
    (P : SpectralMeasurePVMActualBorelFiniteStageObligationPacket) : Prop :=
  ∀ n : ℕ, ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (P.finiteUnion (n + 1)) x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (P.finiteUnion n) x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (P.family (n + 1)) x

/-- The empty recursive finite-stage packet satisfies the finite-stage projection
additivity law. -/
theorem spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_projection_additivity_law :
    SpectralMeasurePVMActualBorelFiniteStageProjectionAdditivityLaw
      (spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
        spectralMeasurePVMActualBorelEmptyCountableFamily) := by
  intro n x
  have hsucc :
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
          ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
            spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion (n + 1)) x = 0 :=
    spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_projection_zero (n + 1) x
  have hprev :
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
          ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
            spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n) x = 0 :=
    spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_projection_zero n x
  have hnext :
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
          (spectralMeasurePVMActualBorelEmptyCountableFamily (n + 1)) x = 0 := by
    exact
      spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_zero_of_underlying_empty
        (spectralMeasurePVMActualBorelEmptyCountableFamily (n + 1))
        (by simp [spectralMeasurePVMActualBorelEmptyCountableFamily,
          spectralMeasurePVMActualBorelEmptySet])
        x
  rw [hsucc, hprev, hnext]
  simp

/-- Finite-stage additivity-obligation target.

The general law is recorded as a predicate on packets.  The empty recursive
packet is the sanity witness that the obligation surface is nonempty. -/
def SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationTarget : Prop :=
  ∃ P : SpectralMeasurePVMActualBorelFiniteStageObligationPacket,
    SpectralMeasurePVMActualBorelFiniteStageProjectionAdditivityLaw P

/-- The finite-stage additivity-obligation target is ready. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_target_ready :
    SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationTarget := by
  exact ⟨
    spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
      spectralMeasurePVMActualBorelEmptyCountableFamily,
    spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_projection_additivity_law⟩

/-- Actual-Borel finite-stage additivity-obligation bridge. -/
def SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelFiniteStageObligationPacketPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel finite-stage additivity-obligation bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_bridge_ready :
    SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_public_boundary_held,
    spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the finite-stage additivity-obligation bridge. -/
def SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationBridgeReady ∧
  SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the finite-stage additivity-obligation bridge is held. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_public_boundary_held :
    SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_bridge_ready,
    spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
