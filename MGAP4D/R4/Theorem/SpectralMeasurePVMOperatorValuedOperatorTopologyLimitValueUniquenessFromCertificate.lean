import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyTailStabilityFromCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Uniqueness of the normalized operator value of the limit slot for eventual-
convergence certificates on the same concrete countable family.

Given two certificates, use the common tail index `c.cutoff + d.cutoff`, viewed
also as `d.cutoff + c.cutoff`, to compare both limit slots to the same finite
partial operator value. -/
theorem spectral_measure_pvm_operator_topology_limit_value_unique_from_certificates
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c d : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) :
    spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot =
      spectralMeasurePVMConcreteNormalizationCandidate d.limitSlot := by
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

/-- Limit-value uniqueness packaged for a concrete countable family. -/
def SpectralMeasurePVMOperatorTopologyLimitValueUniquenessFromCertificate
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  ∀ c d : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
    spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot =
      spectralMeasurePVMConcreteNormalizationCandidate d.limitSlot

/-- Every concrete countable family has uniqueness of normalized limit-slot value
among eventual-convergence certificates. -/
theorem spectral_measure_pvm_operator_topology_limit_value_uniqueness_from_certificate_ready
    (s : SpectralMeasurePVMConcreteCountableFamily) :
    SpectralMeasurePVMOperatorTopologyLimitValueUniquenessFromCertificate s := by
  intro c d
  exact spectral_measure_pvm_operator_topology_limit_value_unique_from_certificates s c d

/-- Limit-value uniqueness together with tail stability and the concrete branch
closure surface. -/
def SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyLimitValueUniquenessFromCertificate s ∧
  SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized branch supplies limit-value uniqueness, tail stability, and the
concrete branch closure surface. -/
theorem spectral_measure_pvm_operator_topology_limit_value_uniqueness_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_limit_value_uniqueness_from_certificate_ready s,
    spectral_measure_pvm_operator_topology_tail_stability_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready s hcase,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family has limit-value uniqueness. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_limit_value_uniqueness_bridge_ready :
    SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_limit_value_uniqueness_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has limit-value uniqueness at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_limit_value_uniqueness_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_limit_value_uniqueness_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: the uniqueness bridge exposes normalized limit-value uniqueness. -/
theorem spectral_measure_pvm_operator_topology_limit_value_uniqueness_bridge_extracts_uniqueness
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady s) :
    SpectralMeasurePVMOperatorTopologyLimitValueUniquenessFromCertificate s := by
  rcases h with ⟨huniq, _, _, _, _⟩
  exact huniq

/-- Projection: the uniqueness bridge exposes tail stability. -/
theorem spectral_measure_pvm_operator_topology_limit_value_uniqueness_bridge_extracts_tail_stability
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady s) :
    SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s := by
  rcases h with ⟨_, htail, _, _, _⟩
  exact htail

/-- Projection: the uniqueness bridge preserves the no-shell-collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_limit_value_uniqueness_bridge_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyLimitValueUniquenessBridgeReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
