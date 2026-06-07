import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchRealizationCases

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- In a pinned single-whole branch, once the finite partial union reaches the
successor of the pinned support, all later finite partial unions remain the whole
index.  This is the concrete eventual-constancy lemma behind the single-whole
operator-topology branch. -/
theorem spectral_measure_pvm_concrete_partial_union_single_whole_eventually_whole
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    ∀ m : Nat,
      SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k + m) s =
        SpectralMeasurePVMConcreteIndex.whole := by
  intro m
  induction m with
  | zero =>
      simpa using
        spectral_measure_pvm_concrete_partial_union_single_whole_at_support s k hs
  | succ m ih =>
      change
        SpectralMeasurePVMConcreteIndexUnion
            (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k + m) s)
            (s (Nat.succ k + m)) =
          SpectralMeasurePVMConcreteIndex.whole
      rw [ih]
      rfl

/-- In a pinned single-whole branch, all finite partial operator sums after the
successor of the support are the identity operator. -/
theorem spectral_measure_pvm_concrete_partial_sum_single_whole_eventually_identity
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    ∀ m : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k + m) s) =
        SpectralMeasurePVMConcreteBoundedOperator.identity := by
  intro m
  rw [spectral_measure_pvm_concrete_partial_union_single_whole_eventually_whole s k hs m]
  rfl

/-- Explicit eventual-constant sequence target for the pinned single-whole branch. -/
def SpectralMeasurePVMOperatorTopologySingleWholeEventuallyConstantIdentitySequence
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat) : Prop :=
  ∀ m : Nat,
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k + m) s) =
      SpectralMeasurePVMConcreteBoundedOperator.identity

/-- The pinned single-whole branch satisfies the explicit eventual-constant
identity sequence target. -/
theorem spectral_measure_pvm_operator_topology_single_whole_eventually_constant_identity_sequence_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologySingleWholeEventuallyConstantIdentitySequence s k := by
  exact spectral_measure_pvm_concrete_partial_sum_single_whole_eventually_identity s k hs

/-- The canonical pinned single-whole family satisfies the explicit
eventual-constant identity sequence target at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_eventually_constant_identity_sequence_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologySingleWholeEventuallyConstantIdentitySequence
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) k := by
  exact spectral_measure_pvm_operator_topology_single_whole_eventually_constant_identity_sequence_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k) k
    (spectral_measure_pvm_concrete_single_whole_at_family_spec k)

/-- The pinned single-whole branch now supplies both the conditional bridge and
the explicit eventual-constant identity sequence. -/
def SpectralMeasurePVMOperatorTopologySingleWholeEventualConstancyBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat) : Prop :=
  SpectralMeasurePVMOperatorTopologySingleWholeEventuallyConstantIdentitySequence s k ∧
  ∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w

/-- The pinned single-whole branch has the eventual-constancy bridge. -/
theorem spectral_measure_pvm_operator_topology_single_whole_eventual_constancy_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologySingleWholeEventualConstancyBridgeReady s k := by
  exact ⟨
    spectral_measure_pvm_operator_topology_single_whole_eventually_constant_identity_sequence_ready s k hs,
    ⟨spectralMeasurePVMOperatorTopologySingleWholeRealizationWitness s k hs,
      spectral_measure_pvm_operator_topology_single_whole_conditional_bridge_ready s k hs⟩⟩

/-- The canonical pinned single-whole family has the eventual-constancy bridge at
any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_eventual_constancy_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologySingleWholeEventualConstancyBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) k := by
  exact spectral_measure_pvm_operator_topology_single_whole_eventual_constancy_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k) k
    (spectral_measure_pvm_concrete_single_whole_at_family_spec k)

end

end Theorem
end R4
end MGAP4D
