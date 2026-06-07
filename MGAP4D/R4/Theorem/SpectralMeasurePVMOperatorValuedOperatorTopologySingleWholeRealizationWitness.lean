import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyAllEmptyRealizationWitness

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- If all entries below a finite cutoff are empty, then the concrete finite
partial union up to that cutoff is empty.  This is the finite prefix lemma needed
for the pinned single-whole countable-additivity branch. -/
theorem spectral_measure_pvm_concrete_partial_union_empty_of_below
    (s : SpectralMeasurePVMConcreteCountableFamily) :
    ∀ N : Nat,
      (∀ n : Nat, n < N → s n = SpectralMeasurePVMConcreteIndex.empty) →
        SpectralMeasurePVMConcreteFinitePartialUnion N s =
          SpectralMeasurePVMConcreteIndex.empty := by
  intro N
  induction N with
  | zero =>
      intro _hbelow
      rfl
  | succ N ih =>
      intro hbelow
      change
        SpectralMeasurePVMConcreteIndexUnion
            (SpectralMeasurePVMConcreteFinitePartialUnion N s) (s N) =
          SpectralMeasurePVMConcreteIndex.empty
      have hprefix :
          SpectralMeasurePVMConcreteFinitePartialUnion N s =
            SpectralMeasurePVMConcreteIndex.empty := by
        exact ih (by
          intro n hn
          exact hbelow n (Nat.lt_trans hn (Nat.lt_succ_self N)))
      have hN : s N = SpectralMeasurePVMConcreteIndex.empty :=
        hbelow N (Nat.lt_succ_self N)
      rw [hprefix, hN]
      rfl

/-- For a pinned single-whole family, the finite partial union at the successor
of the pinned position is the whole index. -/
theorem spectral_measure_pvm_concrete_partial_union_single_whole_at_support
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k) s =
      SpectralMeasurePVMConcreteIndex.whole := by
  rcases hs with ⟨hk, hrest⟩
  change
    SpectralMeasurePVMConcreteIndexUnion
        (SpectralMeasurePVMConcreteFinitePartialUnion k s) (s k) =
      SpectralMeasurePVMConcreteIndex.whole
  have hprefix :
      SpectralMeasurePVMConcreteFinitePartialUnion k s =
        SpectralMeasurePVMConcreteIndex.empty := by
    exact spectral_measure_pvm_concrete_partial_union_empty_of_below s k (by
      intro n hn
      exact hrest n (Nat.ne_of_lt hn))
  rw [hprefix, hk]
  rfl

/-- Actual realization predicate for the pinned single-whole branch: at the
successor of the pinned index, the finite partial operator sum is identity. -/
def SpectralMeasurePVMOperatorTopologySingleWholeActualRealization
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat) : Prop :=
  spectralMeasurePVMConcreteNormalizationCandidate
      (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k) s) =
    SpectralMeasurePVMConcreteBoundedOperator.identity

/-- Limit-slot compatibility for the pinned single-whole branch: the concrete
countable union operator is identity. -/
def SpectralMeasurePVMOperatorTopologySingleWholeLimitSlotCompatibility
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat) : Prop :=
  spectralMeasurePVMConcreteNormalizationCandidate
      (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k) =
    SpectralMeasurePVMConcreteBoundedOperator.identity

/-- The pinned single-whole branch realizes the identity finite partial operator
sum at the successor of the support. -/
theorem spectral_measure_pvm_operator_topology_single_whole_actual_realization_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologySingleWholeActualRealization s k := by
  rw [spectral_measure_pvm_concrete_partial_union_single_whole_at_support s k hs]
  rfl

/-- The pinned single-whole branch gives identity limit-slot compatibility. -/
theorem spectral_measure_pvm_operator_topology_single_whole_limit_slot_compatibility_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologySingleWholeLimitSlotCompatibility s k := by
  exact spectral_measure_pvm_concrete_countable_single_whole_additivity s k hs

/-- Canonical realization witness for a pinned single-whole branch. -/
def spectralMeasurePVMOperatorTopologySingleWholeRealizationWitness
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness :=
  { actualOperatorTopologyRealization :=
      SpectralMeasurePVMOperatorTopologySingleWholeActualRealization s k
    limitSlotRealizationCompatibility :=
      SpectralMeasurePVMOperatorTopologySingleWholeLimitSlotCompatibility s k
    actualOperatorTopologyRealizationReady :=
      spectral_measure_pvm_operator_topology_single_whole_actual_realization_ready s k hs
    limitSlotRealizationCompatibilityReady :=
      spectral_measure_pvm_operator_topology_single_whole_limit_slot_compatibility_ready s k hs }

/-- The pinned single-whole branch instantiates the conditional operator-topology
countable-additivity bridge. -/
theorem spectral_measure_pvm_operator_topology_single_whole_conditional_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady
      (spectralMeasurePVMOperatorTopologySingleWholeRealizationWitness s k hs) := by
  exact spectral_measure_pvm_operator_topology_countable_additivity_conditional_bridge_ready
    (spectralMeasurePVMOperatorTopologySingleWholeRealizationWitness s k hs)

/-- The canonical pinned single-whole family gives a fully instantiated
conditional bridge at any pinned index. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_conditional_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady
      (spectralMeasurePVMOperatorTopologySingleWholeRealizationWitness
        (spectralMeasurePVMConcreteSingleWholeAtFamily k) k
        (spectral_measure_pvm_concrete_single_whole_at_family_spec k)) := by
  exact spectral_measure_pvm_operator_topology_single_whole_conditional_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k) k
    (spectral_measure_pvm_concrete_single_whole_at_family_spec k)

end

end Theorem
end R4
end MGAP4D
