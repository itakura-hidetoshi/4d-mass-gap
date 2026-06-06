import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelRecursiveFinitePartialUnion

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Finite-stage obligation packet for actual-Borel countable families.

It records the finite partial-union carrier and its base/successor laws on the
underlying subsets of `ℝ`.  It is not a countable-union or operator-topology
limit theorem. -/
structure SpectralMeasurePVMActualBorelFiniteStageObligationPacket where
  family : SpectralMeasurePVMActualBorelCountableFamily
  finiteUnion : ℕ → SpectralMeasurePVMActualBorelCarrierSet
  base_underlying : (finiteUnion 0).1 = (family 0).1
  succ_underlying :
    ∀ n : ℕ, (finiteUnion (n + 1)).1 = (finiteUnion n).1 ∪ (family (n + 1)).1

/-- The recursive finite partial-union packet for a given actual-Borel family. -/
def spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
    (F : SpectralMeasurePVMActualBorelCountableFamily) :
    SpectralMeasurePVMActualBorelFiniteStageObligationPacket where
  family := F
  finiteUnion := spectralMeasurePVMActualBorelRecursiveFinitePartialUnion F
  base_underlying := by
    simp [spectralMeasurePVMActualBorelRecursiveFinitePartialUnion]
  succ_underlying := by
    intro n
    simp [spectralMeasurePVMActualBorelRecursiveFinitePartialUnion,
      spectralMeasurePVMActualBorelCarrierSetUnion]

/-- Existence of a finite-stage obligation packet. -/
def SpectralMeasurePVMActualBorelFiniteStageObligationPacketExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMActualBorelFiniteStageObligationPacket

/-- The finite-stage obligation packet exists, using the empty actual-Borel family. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_existence_target_ready :
    SpectralMeasurePVMActualBorelFiniteStageObligationPacketExistenceTarget := by
  exact ⟨
    spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
      spectralMeasurePVMActualBorelEmptyCountableFamily⟩

/-- The empty-family recursive finite-stage packet has empty underlying finite
unions at every finite stage. -/
theorem spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_underlying_empty
    (n : ℕ) :
    ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
        spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n).1 = (∅ : Set ℝ) := by
  exact spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_underlying n

/-- The empty-family recursive finite-stage packet has zero projection at every
finite stage, by the extensional projection law. -/
theorem spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_projection_zero
    (n : ℕ) (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
          spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n) x = 0 := by
  exact
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_zero_of_underlying_empty
      ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
        spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n)
      (spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_underlying_empty n)
      x

/-- Finite-stage obligation-packet target for the actual-Borel carrier. -/
def SpectralMeasurePVMActualBorelFiniteStageObligationPacketTarget : Prop :=
  SpectralMeasurePVMActualBorelFiniteStageObligationPacketExistenceTarget ∧
  (∀ n : ℕ,
    ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
        spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n).1 = (∅ : Set ℝ)) ∧
  (∀ n : ℕ, ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
          spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n) x = 0)

/-- The finite-stage obligation-packet target is ready. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_target_ready :
    SpectralMeasurePVMActualBorelFiniteStageObligationPacketTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_existence_target_ready,
    spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_underlying_empty,
    spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_projection_zero⟩

/-- Actual-Borel finite-stage obligation-packet bridge. -/
def SpectralMeasurePVMActualBorelFiniteStageObligationPacketBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelFiniteStageObligationPacketTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel finite-stage obligation-packet bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_bridge_ready :
    SpectralMeasurePVMActualBorelFiniteStageObligationPacketBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_public_boundary_held,
    spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the finite-stage obligation-packet bridge. -/
def SpectralMeasurePVMActualBorelFiniteStageObligationPacketPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelFiniteStageObligationPacketBridgeReady ∧
  SpectralMeasurePVMActualBorelFiniteStageObligationPacketTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the finite-stage obligation-packet bridge is held. -/
theorem spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_public_boundary_held :
    SpectralMeasurePVMActualBorelFiniteStageObligationPacketPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_bridge_ready,
    spectral_measure_pvm_actual_borel_finite_stage_obligation_packet_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
