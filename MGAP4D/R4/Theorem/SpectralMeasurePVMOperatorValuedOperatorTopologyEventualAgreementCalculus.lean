import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyEventualLimitSlotUniqueness

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Raw eventual agreement implies tail stability without referring to the
structured certificate wrapper. -/
theorem spectral_measure_pvm_operator_topology_eventual_agreement_tail_stability
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (cutoff : Nat)
    (slot : SpectralMeasurePVMConcreteIndex)
    (h : SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s cutoff slot) :
    ∀ m n : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + m) s) =
        spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + n) s) := by
  intro m n
  calc
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + m) s)
        = spectralMeasurePVMConcreteNormalizationCandidate slot :=
          h m
    _ = spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + n) s) :=
          (h n).symm

/-- Raw eventual agreement is stable under shifting the cutoff forward. -/
theorem spectral_measure_pvm_operator_topology_eventual_agreement_shift_cutoff
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (cutoff q : Nat)
    (slot : SpectralMeasurePVMConcreteIndex)
    (h : SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s cutoff slot) :
    SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s (cutoff + q) slot := by
  intro m
  simpa [Nat.add_assoc] using h (q + m)

/-- Raw eventual agreement at cutoff zero can be read at every finite partial
index directly. -/
theorem spectral_measure_pvm_operator_topology_eventual_agreement_zero_cutoff_apply
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (slot : SpectralMeasurePVMConcreteIndex)
    (h : SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s 0 slot) :
    ∀ N : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion N s) =
        spectralMeasurePVMConcreteNormalizationCandidate slot := by
  intro N
  simpa using h N

/-- The raw eventual agreement induced by a structured certificate also gives raw
tail stability. -/
theorem spectral_measure_pvm_operator_topology_certificate_raw_tail_stability
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) :
    ∀ m n : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + m) s) =
        spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + n) s) := by
  exact spectral_measure_pvm_operator_topology_eventual_agreement_tail_stability
    s c.cutoff c.limitSlot
    (spectral_measure_pvm_operator_topology_certificate_eventually_agrees_with_slot s c)

/-- Eventual agreement calculus package: uniqueness, shift stability, raw tail
stability, and compatibility with the concrete operator-topology convergence
target are all available for any concrete countable family. -/
def SpectralMeasurePVMOperatorTopologyEventualAgreementCalculusReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyEventuallyUniqueLimitSlot s ∧
  (∀ cutoff : Nat,
    ∀ slot : SpectralMeasurePVMConcreteIndex,
      SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s cutoff slot →
        ∀ m n : Nat,
          spectralMeasurePVMConcreteNormalizationCandidate
              (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + m) s) =
            spectralMeasurePVMConcreteNormalizationCandidate
              (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + n) s)) ∧
  (∀ cutoff q : Nat,
    ∀ slot : SpectralMeasurePVMConcreteIndex,
      SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s cutoff slot →
        SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s (cutoff + q) slot) ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The raw eventual agreement calculus package is ready. -/
theorem spectral_measure_pvm_operator_topology_eventual_agreement_calculus_ready
    (s : SpectralMeasurePVMConcreteCountableFamily) :
    SpectralMeasurePVMOperatorTopologyEventualAgreementCalculusReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_eventually_unique_limit_slot_ready s,
    (by
      intro cutoff slot h m n
      exact spectral_measure_pvm_operator_topology_eventual_agreement_tail_stability s cutoff slot h m n),
    (by
      intro cutoff q slot h
      exact spectral_measure_pvm_operator_topology_eventual_agreement_shift_cutoff s cutoff q slot h),
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Batch bridge: a realized concrete branch supplies the raw eventual agreement
calculus, the structured uniqueness bridge, tail stability, and the concrete
branch closure surface at once. -/
def SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyEventualAgreementCalculusReady s ∧
  SpectralMeasurePVMOperatorTopologyEventualLimitSlotUniquenessBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyLimitSlotUniquenessBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyTailStabilityBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized concrete branch supplies the whole eventual-agreement batch bridge. -/
theorem spectral_measure_pvm_operator_topology_eventual_agreement_batch_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_eventual_agreement_calculus_ready s,
    spectral_measure_pvm_operator_topology_eventual_limit_slot_uniqueness_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_limit_slot_uniqueness_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_tail_stability_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready s hcase,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family supplies the whole eventual-agreement
batch bridge. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_eventual_agreement_batch_bridge_ready :
    SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_eventual_agreement_batch_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family supplies the whole eventual-
agreement batch bridge at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_eventual_agreement_batch_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_eventual_agreement_batch_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
