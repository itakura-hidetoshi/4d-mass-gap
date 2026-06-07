import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyTailStabilityFromCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Limit-slot uniqueness for eventual-convergence certificates over the same
concrete countable family.

If two certificates both say that the same finite partial operator sequence is
eventually equal to their respective limit slots, then the two normalized limit
slots agree.  The proof compares both certificates at the common tail index
`c.cutoff + d.cutoff` / `d.cutoff + c.cutoff`. -/
def SpectralMeasurePVMOperatorTopologyLimitSlotUniqueForCertificates
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  ∀ c d : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
    spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot =
      spectralMeasurePVMConcreteNormalizationCandidate d.limitSlot

/-- Any two eventual-convergence certificates for the same concrete countable
family have the same normalized limit slot. -/
theorem spectral_measure_pvm_operator_topology_limit_slot_unique_for_certificates_ready
    (s : SpectralMeasurePVMConcreteCountableFamily) :
    SpectralMeasurePVMOperatorTopologyLimitSlotUniqueForCertificates s := by
  intro c d
  calc
    spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot
        = spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + d.cutoff) s) :=
          (c.eventually_agrees_with_limit_slot d.cutoff).symm
    _ = spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (d.cutoff + c.cutoff) s) := by
          rw [Nat.add_comm c.cutoff d.cutoff]
    _ = spectralMeasurePVMConcreteNormalizationCandidate d.limitSlot :=
          d.eventually_agrees_with_limit_slot c.cutoff

/-- Limit-slot uniqueness together with the tail-stability bridge. -/
def SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyLimitSlotUniqueForCertificates s ∧
  SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized branch supplies limit-slot uniqueness, tail stability, and the
concrete branch closure surface. -/
theorem spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_limit_slot_unique_for_certificates_ready s,
    spectral_measure_pvm_operator_topology_tail_stability_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready s hcase,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family has limit-slot uniqueness. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_limit_slot_uniqueness_bridge_ready :
    SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has limit-slot uniqueness at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_limit_slot_uniqueness_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: limit-slot uniqueness bridge exposes uniqueness of normalized
limit slots. -/
theorem spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_extracts_uniqueness
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady s) :
    SpectralMeasurePVMOperatorTopologyLimitSlotUniqueForCertificates s := by
  rcases h with ⟨hunique, _, _, _, _⟩
  exact hunique

/-- Projection: limit-slot uniqueness bridge exposes tail stability. -/
theorem spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_extracts_tail_stability
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady s) :
    SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s := by
  rcases h with ⟨_, htail, _, _, _⟩
  exact htail

/-- Projection: limit-slot uniqueness bridge preserves the no-shell-collapse
boundary. -/
theorem spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
