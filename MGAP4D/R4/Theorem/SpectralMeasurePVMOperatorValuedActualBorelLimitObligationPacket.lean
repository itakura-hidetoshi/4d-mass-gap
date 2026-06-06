import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelFiniteStageAdditivityObligation

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Limit-obligation packet for the actual-Borel path.

This packet records a finite-stage packet, a proposed limit carrier, the
finite-stage additivity law, and a monotone underlying-set bound into the
proposed limit carrier.  It is only an obligation surface; it does not prove any
operator-topology convergence. -/
structure SpectralMeasurePVMActualBorelLimitObligationPacket where
  finitePacket : SpectralMeasurePVMActualBorelFiniteStageObligationPacket
  limitCarrier : SpectralMeasurePVMActualBorelCarrierSet
  finite_stage_law :
    SpectralMeasurePVMActualBorelFiniteStageProjectionAdditivityLaw finitePacket
  finite_underlying_bounded_by_limit :
    ∀ n : ℕ, (finitePacket.finiteUnion n).1 ⊆ limitCarrier.1
  limit_projection_zero :
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap limitCarrier x = 0

/-- Empty-family witness for the actual-Borel limit-obligation packet. -/
def spectralMeasurePVMActualBorelEmptyLimitObligationPacket :
    SpectralMeasurePVMActualBorelLimitObligationPacket where
  finitePacket :=
    spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
      spectralMeasurePVMActualBorelEmptyCountableFamily
  limitCarrier := spectralMeasurePVMActualBorelEmptySet
  finite_stage_law :=
    spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_projection_additivity_law
  finite_underlying_bounded_by_limit := by
    intro n x hx
    have hfinite :
        ((spectralMeasurePVMActualBorelRecursiveFiniteStageObligationPacket
          spectralMeasurePVMActualBorelEmptyCountableFamily).finiteUnion n).1 =
          (∅ : Set ℝ) :=
      spectral_measure_pvm_actual_borel_empty_recursive_finite_stage_packet_underlying_empty n
    rw [hfinite] at hx
    simpa [spectralMeasurePVMActualBorelEmptySet] using hx
  limit_projection_zero := by
    intro x
    exact
      spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_zero_of_underlying_empty
        spectralMeasurePVMActualBorelEmptySet
        (by rfl)
        x

/-- Existence target for the actual-Borel limit-obligation packet. -/
def SpectralMeasurePVMActualBorelLimitObligationPacketExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMActualBorelLimitObligationPacket

/-- The actual-Borel limit-obligation packet exists. -/
theorem spectral_measure_pvm_actual_borel_limit_obligation_packet_existence_target_ready :
    SpectralMeasurePVMActualBorelLimitObligationPacketExistenceTarget := by
  exact ⟨spectralMeasurePVMActualBorelEmptyLimitObligationPacket⟩

/-- Empty limit packet has zero projection at the proposed limit carrier. -/
theorem spectral_measure_pvm_actual_borel_empty_limit_obligation_packet_projection_zero
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptyLimitObligationPacket.limitCarrier x = 0 := by
  exact spectralMeasurePVMActualBorelEmptyLimitObligationPacket.limit_projection_zero x

/-- Empty limit packet bounds all finite stages by the proposed limit carrier. -/
theorem spectral_measure_pvm_actual_borel_empty_limit_obligation_packet_finite_bound
    (n : ℕ) :
    (spectralMeasurePVMActualBorelEmptyLimitObligationPacket.finitePacket.finiteUnion n).1 ⊆
      spectralMeasurePVMActualBorelEmptyLimitObligationPacket.limitCarrier.1 := by
  exact spectralMeasurePVMActualBorelEmptyLimitObligationPacket.finite_underlying_bounded_by_limit n

/-- Actual-Borel limit-obligation target. -/
def SpectralMeasurePVMActualBorelLimitObligationPacketTarget : Prop :=
  SpectralMeasurePVMActualBorelLimitObligationPacketExistenceTarget ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptyLimitObligationPacket.limitCarrier x = 0) ∧
  (∀ n : ℕ,
    (spectralMeasurePVMActualBorelEmptyLimitObligationPacket.finitePacket.finiteUnion n).1 ⊆
      spectralMeasurePVMActualBorelEmptyLimitObligationPacket.limitCarrier.1)

/-- The actual-Borel limit-obligation target is ready. -/
theorem spectral_measure_pvm_actual_borel_limit_obligation_packet_target_ready :
    SpectralMeasurePVMActualBorelLimitObligationPacketTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_limit_obligation_packet_existence_target_ready,
    spectral_measure_pvm_actual_borel_empty_limit_obligation_packet_projection_zero,
    spectral_measure_pvm_actual_borel_empty_limit_obligation_packet_finite_bound⟩

/-- Actual-Borel limit-obligation bridge. -/
def SpectralMeasurePVMActualBorelLimitObligationPacketBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelFiniteStageAdditivityObligationPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelLimitObligationPacketTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel limit-obligation bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_limit_obligation_packet_bridge_ready :
    SpectralMeasurePVMActualBorelLimitObligationPacketBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_stage_additivity_obligation_public_boundary_held,
    spectral_measure_pvm_actual_borel_limit_obligation_packet_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel limit-obligation bridge. -/
def SpectralMeasurePVMActualBorelLimitObligationPacketPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelLimitObligationPacketBridgeReady ∧
  SpectralMeasurePVMActualBorelLimitObligationPacketTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel limit-obligation bridge is held. -/
theorem spectral_measure_pvm_actual_borel_limit_obligation_packet_public_boundary_held :
    SpectralMeasurePVMActualBorelLimitObligationPacketPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_limit_obligation_packet_bridge_ready,
    spectral_measure_pvm_actual_borel_limit_obligation_packet_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
