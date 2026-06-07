import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyConcreteBranchClosureSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Tail stability extracted from an eventual-convergence certificate.

If the finite partial operator sequence agrees with the same limit slot after a
cutoff, then any two tail entries agree with each other.  This is the concrete
Cauchy/stability computation needed before passing to a genuine operator-
topology limit theorem. -/
def SpectralMeasurePVMOperatorTopologyTailStabilityFromCertificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) : Prop :=
  ∀ m n : Nat,
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + m) s) =
      spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + n) s)

/-- An eventual-convergence certificate gives tail stability of the finite
partial operator sequence. -/
theorem spectral_measure_pvm_operator_topology_tail_stability_from_certificate_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) :
    SpectralMeasurePVMOperatorTopologyTailStabilityFromCertificate s c := by
  intro m n
  calc
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + m) s)
        = spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot :=
          c.eventually_agrees_with_limit_slot m
    _ = spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + n) s) :=
          (c.eventually_agrees_with_limit_slot n).symm

/-- A realized branch has some tail-stability certificate. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_tail_stability_certificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    ∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
      SpectralMeasurePVMOperatorTopologyTailStabilityFromCertificate s c := by
  rcases spectral_measure_pvm_operator_topology_branch_realization_case_eventual_convergence_certificate s hcase with
    ⟨c, _⟩
  exact ⟨c, spectral_measure_pvm_operator_topology_tail_stability_from_certificate_ready s c⟩

/-- Tail stability together with the concrete branch closure surface. -/
def SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  (∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
    SpectralMeasurePVMOperatorTopologyTailStabilityFromCertificate s c) ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized branch supplies tail stability, the concrete branch closure
surface, and the operator-topology convergence target. -/
theorem spectral_measure_pvm_operator_topology_tail_stability_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_realization_case_tail_stability_certificate s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready s hcase,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family has tail stability. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_tail_stability_bridge_ready :
    SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_tail_stability_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has tail stability at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_tail_stability_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_tail_stability_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: tail-stability bridge exposes the tail-stability certificate. -/
theorem spectral_measure_pvm_operator_topology_tail_stability_bridge_extracts_certificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s) :
    ∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
      SpectralMeasurePVMOperatorTopologyTailStabilityFromCertificate s c := by
  rcases h with ⟨hstable, _, _, _⟩
  exact hstable

/-- Projection: tail-stability bridge exposes the concrete branch closure surface. -/
theorem spectral_measure_pvm_operator_topology_tail_stability_bridge_extracts_closure_surface
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s := by
  rcases h with ⟨_, hclosure, _, _⟩
  exact hclosure

/-- Projection: tail-stability bridge preserves the no-shell-collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_tail_stability_bridge_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
