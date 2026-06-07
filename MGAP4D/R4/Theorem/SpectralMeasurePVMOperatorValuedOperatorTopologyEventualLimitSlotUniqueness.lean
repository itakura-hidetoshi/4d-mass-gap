import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyLimitSlotUniquenessFromCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A raw eventual agreement relation between the concrete finite-partial
operator sequence and a chosen limit slot.

Unlike `SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate`,
this predicate does not package the cutoff and limit slot into a structure.  It
is the direct convergence-calculus statement used for uniqueness of eventual
limit slots. -/
def SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (cutoff : Nat)
    (limitSlot : SpectralMeasurePVMConcreteIndex) : Prop :=
  ∀ m : Nat,
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + m) s) =
      spectralMeasurePVMConcreteNormalizationCandidate limitSlot

/-- Raw eventual limit-slot uniqueness: if the same finite-partial sequence is
eventually equal to two candidate limit slots, then the normalized limit slots
are equal. -/
def SpectralMeasurePVMOperatorTopologyEventuallyUniqueLimitSlot
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  ∀ cutoffA cutoffB : Nat,
    ∀ slotA slotB : SpectralMeasurePVMConcreteIndex,
      SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s cutoffA slotA →
      SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s cutoffB slotB →
        spectralMeasurePVMConcreteNormalizationCandidate slotA =
          spectralMeasurePVMConcreteNormalizationCandidate slotB

/-- The raw eventual limit slot is unique.  The proof compares the two eventual
agreements at a common tail index. -/
theorem spectral_measure_pvm_operator_topology_eventually_unique_limit_slot_ready
    (s : SpectralMeasurePVMConcreteCountableFamily) :
    SpectralMeasurePVMOperatorTopologyEventuallyUniqueLimitSlot s := by
  intro cutoffA cutoffB slotA slotB hA hB
  calc
    spectralMeasurePVMConcreteNormalizationCandidate slotA
        = spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (cutoffA + cutoffB) s) :=
          (hA cutoffB).symm
    _ = spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (cutoffB + cutoffA) s) := by
          rw [Nat.add_comm cutoffA cutoffB]
    _ = spectralMeasurePVMConcreteNormalizationCandidate slotB :=
          hB cutoffA

/-- Every structured eventual-convergence certificate induces the raw eventual
agreement predicate. -/
theorem spectral_measure_pvm_operator_topology_certificate_eventually_agrees_with_slot
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) :
    SpectralMeasurePVMOperatorTopologyEventuallyAgreesWithSlot s c.cutoff c.limitSlot := by
  exact c.eventually_agrees_with_limit_slot

/-- The raw uniqueness theorem recovers the structured certificate uniqueness. -/
theorem spectral_measure_pvm_operator_topology_eventual_uniqueness_recovers_certificate_uniqueness
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c d : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) :
    spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot =
      spectralMeasurePVMConcreteNormalizationCandidate d.limitSlot := by
  exact spectral_measure_pvm_operator_topology_eventually_unique_limit_slot_ready s
    c.cutoff d.cutoff c.limitSlot d.limitSlot
    (spectral_measure_pvm_operator_topology_certificate_eventually_agrees_with_slot s c)
    (spectral_measure_pvm_operator_topology_certificate_eventually_agrees_with_slot s d)

/-- Raw eventual limit-slot uniqueness together with the previous structured
limit-slot uniqueness bridge. -/
def SpectralMeasurePVMOperatorTopologyEventualLimitSlotUniquenessBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyEventuallyUniqueLimitSlot s ∧
  SpectralMeasurePVMOperatorTopologyLimitSlotUniqueForCertificates s ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized branch supplies raw eventual limit-slot uniqueness and the
structured certificate uniqueness bridge. -/
theorem spectral_measure_pvm_operator_topology_eventual_limit_slot_uniqueness_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (_hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyEventualLimitSlotUniquenessBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_eventually_unique_limit_slot_ready s,
    spectral_measure_pvm_operator_topology_limit_slot_unique_for_certificates_ready s,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family has raw eventual limit-slot uniqueness. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_eventual_limit_slot_uniqueness_bridge_ready :
    SpectralMeasurePVMOperatorTopologyEventualLimitSlotUniquenessBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_eventual_limit_slot_uniqueness_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has raw eventual limit-slot
uniqueness at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_eventual_limit_slot_uniqueness_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyEventualLimitSlotUniquenessBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_eventual_limit_slot_uniqueness_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
