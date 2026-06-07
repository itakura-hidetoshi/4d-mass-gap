import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchEventualConstancy

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Unified limit-slot agreement target for the two currently realized concrete
operator-topology branches.

The all-empty branch has every finite partial operator equal to the same zero
operator as its countable-union slot.  The pinned single-whole branch has every
finite partial operator after the support successor equal to the same identity
operator as its countable-union slot. -/
def SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  (SpectralMeasurePVMConcreteAllEmptyFamily s ∧
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteCountableUnionAllEmpty s) =
      SpectralMeasurePVMConcreteBoundedOperator.zero ∧
    ∀ N : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion N s) =
        spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteCountableUnionAllEmpty s)) ∨
  (∃ k : Nat,
    SpectralMeasurePVMConcreteSingleWholeAt s k ∧
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k) =
        SpectralMeasurePVMConcreteBoundedOperator.identity ∧
      ∀ m : Nat,
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k + m) s) =
          spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k))

/-- The all-empty branch has exact agreement between every finite partial
operator and the countable-union zero slot. -/
theorem spectral_measure_pvm_operator_topology_all_empty_branch_limit_slot_agreement
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement s := by
  have hlim :
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteCountableUnionAllEmpty s) =
        SpectralMeasurePVMConcreteBoundedOperator.zero :=
    spectral_measure_pvm_concrete_countable_all_empty_additivity s hs
  have hseq :
      ∀ N : Nat,
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion N s) =
          spectralMeasurePVMConcreteBoundedOperator.zero :=
    spectral_measure_pvm_concrete_partial_sum_all_empty_zero s hs
  refine Or.inl ⟨hs, hlim, ?_⟩
  intro N
  rw [hseq N, hlim]

/-- The pinned single-whole branch has exact agreement between the tail finite
partial identity operators and the countable-union identity slot. -/
theorem spectral_measure_pvm_operator_topology_single_whole_branch_limit_slot_agreement
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement s := by
  have hlim :
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k) =
        SpectralMeasurePVMConcreteBoundedOperator.identity :=
    spectral_measure_pvm_concrete_countable_single_whole_additivity s k hs
  have hseq :
      SpectralMeasurePVMOperatorTopologySingleWholeEventuallyConstantIdentitySequence s k :=
    spectral_measure_pvm_operator_topology_single_whole_eventually_constant_identity_sequence_ready s k hs
  refine Or.inr ⟨k, hs, hlim, ?_⟩
  intro m
  rw [hseq m, hlim]

/-- Every realized concrete operator-topology branch has exact finite-partial to
countable-union limit-slot agreement. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_limit_slot_agreement
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement s := by
  cases hcase with
  | allEmpty hs =>
      exact spectral_measure_pvm_operator_topology_all_empty_branch_limit_slot_agreement s hs
  | singleWholeAt k hs =>
      exact spectral_measure_pvm_operator_topology_single_whole_branch_limit_slot_agreement s k hs

/-- Branch limit-slot agreement together with the already constructed branch
conditional bridge. -/
def SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement s ∧
  SpectralMeasurePVMOperatorTopologyBranchEventualConstancyBridgeReady s

/-- A realized branch supplies exact limit-slot agreement and the conditional
operator-topology bridge. -/
theorem spectral_measure_pvm_operator_topology_branch_limit_slot_agreement_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_realization_case_limit_slot_agreement s hcase,
    spectral_measure_pvm_operator_topology_branch_eventual_constancy_bridge_ready s hcase⟩

/-- The canonical empty countable family has exact finite-partial to
countable-union limit-slot agreement and the conditional bridge. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_limit_slot_agreement_bridge_ready :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_limit_slot_agreement_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has exact tail finite-partial to
countable-union limit-slot agreement and the conditional bridge at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_limit_slot_agreement_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_limit_slot_agreement_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
