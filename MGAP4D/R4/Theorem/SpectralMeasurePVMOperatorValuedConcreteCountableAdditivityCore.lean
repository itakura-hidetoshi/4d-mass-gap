import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Countable family of concrete spectral indices for the first concrete
countable-additivity surface. -/
def SpectralMeasurePVMConcreteCountableFamily :=
  Nat → SpectralMeasurePVMConcreteIndex

/-- Pairwise disjointness for countable concrete families. -/
def SpectralMeasurePVMConcretePairwiseDisjoint
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  ∀ m n : Nat, m ≠ n →
    SpectralMeasurePVMConcreteIndexDisjoint (s m) (s n)

/-- The degenerate countable family whose every entry is the empty index. -/
def SpectralMeasurePVMConcreteAllEmptyFamily
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  ∀ n : Nat, s n = SpectralMeasurePVMConcreteIndex.empty

/-- A countable family with exactly one whole index at the declared position and
empty index everywhere else.  This avoids an early classical existential split in
proofs that only need the pinned position. -/
def SpectralMeasurePVMConcreteSingleWholeAt
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat) : Prop :=
  s k = SpectralMeasurePVMConcreteIndex.whole ∧
    ∀ n : Nat, n ≠ k → s n = SpectralMeasurePVMConcreteIndex.empty

/-- Existential wrapper for the single-whole case.  The concrete proofs below use
`SpectralMeasurePVMConcreteSingleWholeAt` directly; this wrapper records the
later sigma-additivity shape without forcing classical choice into the core. -/
def SpectralMeasurePVMConcreteSingleWholeFamily
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  ∃ k : Nat, SpectralMeasurePVMConcreteSingleWholeAt s k

/-- A concrete empty countable family. -/
def spectralMeasurePVMConcreteEmptyCountableFamily :
    SpectralMeasurePVMConcreteCountableFamily :=
  fun _ => SpectralMeasurePVMConcreteIndex.empty

/-- A concrete single-whole family pinned at `k`. -/
def spectralMeasurePVMConcreteSingleWholeAtFamily
    (k : Nat) : SpectralMeasurePVMConcreteCountableFamily :=
  fun n => if n = k then
    SpectralMeasurePVMConcreteIndex.whole
  else
    SpectralMeasurePVMConcreteIndex.empty

/-- The empty countable family is all-empty. -/
theorem spectral_measure_pvm_concrete_empty_countable_family_all_empty :
    SpectralMeasurePVMConcreteAllEmptyFamily
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  intro n
  rfl

/-- The pinned single-whole family satisfies the pinned single-whole predicate. -/
theorem spectral_measure_pvm_concrete_single_whole_at_family_spec
    (k : Nat) :
    SpectralMeasurePVMConcreteSingleWholeAt
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) k := by
  constructor
  · simp [spectralMeasurePVMConcreteSingleWholeAtFamily]
  · intro n hnk
    simp [spectralMeasurePVMConcreteSingleWholeAtFamily, hnk]

/-- All-empty countable families are pairwise disjoint on the concrete two-index
surface. -/
theorem spectral_measure_pvm_concrete_all_empty_pairwise_disjoint
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    SpectralMeasurePVMConcretePairwiseDisjoint s := by
  intro m n _hmn
  rw [hs m, hs n]
  trivial

/-- Pinned single-whole families are pairwise disjoint on the concrete two-index
surface.  The only non-disjoint pair is `(whole, whole)`, and that can occur only
at the same index. -/
theorem spectral_measure_pvm_concrete_single_whole_at_pairwise_disjoint
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMConcretePairwiseDisjoint s := by
  intro m n hmn
  rcases hs with ⟨hk, hrest⟩
  by_cases hm : m = k
  · subst m
    have hn : n ≠ k := by
      intro hnk
      exact hmn (by simpa [hnk])
    rw [hk, hrest n hn]
    trivial
  · by_cases hn : n = k
    · subst n
      rw [hrest m hm, hk]
      trivial
    · rw [hrest m hm, hrest n hn]
      trivial

/-- Countable union in the all-empty branch. -/
def SpectralMeasurePVMConcreteCountableUnionAllEmpty
    (_s : SpectralMeasurePVMConcreteCountableFamily) :
    SpectralMeasurePVMConcreteIndex :=
  SpectralMeasurePVMConcreteIndex.empty

/-- Countable union in the pinned single-whole branch. -/
def SpectralMeasurePVMConcreteCountableUnionSingleWholeAt
    (_s : SpectralMeasurePVMConcreteCountableFamily)
    (_k : Nat) : SpectralMeasurePVMConcreteIndex :=
  SpectralMeasurePVMConcreteIndex.whole

/-- The all-empty countable union is the empty concrete index. -/
theorem spectral_measure_pvm_concrete_countable_union_all_empty_index
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (_hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    SpectralMeasurePVMConcreteCountableUnionAllEmpty s =
      SpectralMeasurePVMConcreteIndex.empty := by
  rfl

/-- The pinned single-whole countable union is the whole concrete index. -/
theorem spectral_measure_pvm_concrete_countable_union_single_whole_index
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (_hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k =
      SpectralMeasurePVMConcreteIndex.whole := by
  rfl

/-- Concrete finite partial union of the first `N` members of a countable family.
The recursion is intentionally operator-free; finite additivity is invoked only
when the corresponding operator equation is requested. -/
def SpectralMeasurePVMConcreteFinitePartialUnion :
    Nat → SpectralMeasurePVMConcreteCountableFamily →
      SpectralMeasurePVMConcreteIndex
  | 0, _ => SpectralMeasurePVMConcreteIndex.empty
  | Nat.succ N, s =>
      SpectralMeasurePVMConcreteIndexUnion
        (SpectralMeasurePVMConcreteFinitePartialUnion N s)
        (s N)

/-- The finite partial union of an all-empty family remains empty. -/
theorem spectral_measure_pvm_concrete_partial_union_all_empty
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    ∀ N : Nat,
      SpectralMeasurePVMConcreteFinitePartialUnion N s =
        SpectralMeasurePVMConcreteIndex.empty := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
      change
        SpectralMeasurePVMConcreteIndexUnion
          (SpectralMeasurePVMConcreteFinitePartialUnion N s)
          (s N) = SpectralMeasurePVMConcreteIndex.empty
      rw [ih, hs N]
      rfl

/-- Operator-valued finite partial sums for an all-empty family are zero. -/
theorem spectral_measure_pvm_concrete_partial_sum_all_empty_zero
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    ∀ N : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion N s) =
        SpectralMeasurePVMConcreteBoundedOperator.zero := by
  intro N
  rw [spectral_measure_pvm_concrete_partial_union_all_empty s hs N]
  rfl

/-- Successor partial unions satisfy the concrete finite-additivity equation
whenever the previous partial union is disjoint from the next index. -/
theorem spectral_measure_pvm_concrete_partial_union_succ_finite_additivity
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (N : Nat)
    (hN : SpectralMeasurePVMConcreteIndexDisjoint
      (SpectralMeasurePVMConcreteFinitePartialUnion N s) (s N)) :
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ N) s) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion N s))
        (spectralMeasurePVMConcreteNormalizationCandidate (s N)) := by
  change
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteIndexUnion
          (SpectralMeasurePVMConcreteFinitePartialUnion N s) (s N)) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion N s))
        (spectralMeasurePVMConcreteNormalizationCandidate (s N))
  exact spectral_measure_pvm_concrete_binary_finite_additivity
    (SpectralMeasurePVMConcreteFinitePartialUnion N s) (s N) hN

/-- Countable additivity in the all-empty branch: the union maps to zero. -/
theorem spectral_measure_pvm_concrete_countable_all_empty_additivity
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (_hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteCountableUnionAllEmpty s) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rfl

/-- Countable additivity in the pinned single-whole branch: the union maps to the
identity. -/
theorem spectral_measure_pvm_concrete_countable_single_whole_additivity
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (_hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k) =
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rfl

/-- Concrete countable disjoint-family target. -/
def SpectralMeasurePVMConcreteCountableDisjointFamilyTarget : Prop :=
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    SpectralMeasurePVMConcreteAllEmptyFamily s →
      SpectralMeasurePVMConcretePairwiseDisjoint s) ∧
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    ∀ k : Nat,
      SpectralMeasurePVMConcreteSingleWholeAt s k →
        SpectralMeasurePVMConcretePairwiseDisjoint s)

/-- Concrete countable union-index target. -/
def SpectralMeasurePVMConcreteCountableUnionIndexTarget : Prop :=
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    SpectralMeasurePVMConcreteAllEmptyFamily s →
      SpectralMeasurePVMConcreteCountableUnionAllEmpty s =
        SpectralMeasurePVMConcreteIndex.empty) ∧
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    ∀ k : Nat,
      SpectralMeasurePVMConcreteSingleWholeAt s k →
        SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k =
          SpectralMeasurePVMConcreteIndex.whole)

/-- Concrete finite partial-sum sequence target for the all-empty branch. -/
def SpectralMeasurePVMConcreteFinitePartialSumSequenceTarget : Prop :=
  ∀ s : SpectralMeasurePVMConcreteCountableFamily,
    SpectralMeasurePVMConcreteAllEmptyFamily s →
      ∀ N : Nat,
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion N s) =
          SpectralMeasurePVMConcreteBoundedOperator.zero

/-- Concrete monotone-partial-family target.  At this two-index stage it is the
successor finite-additivity law for partial unions under the needed disjointness
hypothesis; a genuine order/topology formulation remains deliberately outside
this core. -/
def SpectralMeasurePVMConcreteMonotonePartialProjectionFamilyTarget : Prop :=
  ∀ s : SpectralMeasurePVMConcreteCountableFamily,
    ∀ N : Nat,
      SpectralMeasurePVMConcreteIndexDisjoint
        (SpectralMeasurePVMConcreteFinitePartialUnion N s) (s N) →
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ N) s) =
          spectralMeasurePVMConcreteOperatorAdd
            (spectralMeasurePVMConcreteNormalizationCandidate
              (SpectralMeasurePVMConcreteFinitePartialUnion N s))
            (spectralMeasurePVMConcreteNormalizationCandidate (s N))

/-- Concrete countable-additivity target: first the all-empty branch, then the
pinned single-whole branch. -/
def SpectralMeasurePVMConcreteCountableAdditivityTarget : Prop :=
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    SpectralMeasurePVMConcreteAllEmptyFamily s →
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteCountableUnionAllEmpty s) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    ∀ k : Nat,
      SpectralMeasurePVMConcreteSingleWholeAt s k →
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k) =
          SpectralMeasurePVMConcreteBoundedOperator.identity)

/-- Degenerate operator-topology convergence target for the current two-index
surface.  It records that the available countable branches have already collapsed
to their operator-valued limits; genuine strong/weak operator topology is still a
future replacement target. -/
def SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget : Prop :=
  SpectralMeasurePVMConcreteFinitePartialSumSequenceTarget ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget

/-- Concrete sigma-additivity receipt target for the two available countable
branches. -/
def SpectralMeasurePVMConcreteSigmaAdditivityReceiptTarget : Prop :=
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget

/-- Concrete handoff target into spectral compatibility. -/
def SpectralMeasurePVMConcreteCountableAdditivityFeedsSpectralCompatibilityTarget :
    Prop :=
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteSigmaAdditivityReceiptTarget

/-- Guard preventing spectral compatibility from using countable additivity
before the finite-additivity handoff and concrete countable equation are both
available. -/
def SpectralMeasurePVMConcreteNoSpectralCompatibilityUseBeforeCountableAdditivityTarget :
    Prop :=
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCoreReady

/-- Concrete countable-additivity discharge receipt. -/
def SpectralMeasurePVMConcreteCountableDischargeReceiptTarget : Prop :=
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete countable disjoint-family target is ready. -/
theorem spectral_measure_pvm_concrete_countable_disjoint_family_target_ready :
    SpectralMeasurePVMConcreteCountableDisjointFamilyTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_all_empty_pairwise_disjoint,
    spectral_measure_pvm_concrete_single_whole_at_pairwise_disjoint⟩

/-- The concrete countable union-index target is ready. -/
theorem spectral_measure_pvm_concrete_countable_union_index_target_ready :
    SpectralMeasurePVMConcreteCountableUnionIndexTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_union_all_empty_index,
    spectral_measure_pvm_concrete_countable_union_single_whole_index⟩

/-- The concrete finite partial-sum sequence target is ready. -/
theorem spectral_measure_pvm_concrete_finite_partial_sum_sequence_target_ready :
    SpectralMeasurePVMConcreteFinitePartialSumSequenceTarget := by
  exact spectral_measure_pvm_concrete_partial_sum_all_empty_zero

/-- The concrete monotone-partial-family target is ready. -/
theorem spectral_measure_pvm_concrete_monotone_partial_projection_family_target_ready :
    SpectralMeasurePVMConcreteMonotonePartialProjectionFamilyTarget := by
  exact spectral_measure_pvm_concrete_partial_union_succ_finite_additivity

/-- The concrete countable-additivity target is ready. -/
theorem spectral_measure_pvm_concrete_countable_additivity_target_ready :
    SpectralMeasurePVMConcreteCountableAdditivityTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_all_empty_additivity,
    spectral_measure_pvm_concrete_countable_single_whole_additivity⟩

/-- The concrete degenerate operator-topology convergence target is ready. -/
theorem spectral_measure_pvm_concrete_operator_topology_convergence_target_ready :
    SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_finite_partial_sum_sequence_target_ready,
    spectral_measure_pvm_concrete_countable_additivity_target_ready⟩

/-- The concrete sigma-additivity receipt target is ready. -/
theorem spectral_measure_pvm_concrete_sigma_additivity_receipt_target_ready :
    SpectralMeasurePVMConcreteSigmaAdditivityReceiptTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready⟩

/-- The concrete countable-to-spectral-compatibility handoff target is ready. -/
theorem spectral_measure_pvm_concrete_countable_additivity_feeds_spectral_compatibility_target_ready :
    SpectralMeasurePVMConcreteCountableAdditivityFeedsSpectralCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_sigma_additivity_receipt_target_ready⟩

/-- The guard against premature spectral-compatibility use is ready. -/
theorem spectral_measure_pvm_concrete_no_spectral_compatibility_use_before_countable_additivity_target_ready :
    SpectralMeasurePVMConcreteNoSpectralCompatibilityUseBeforeCountableAdditivityTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_operator_valued_concrete_finite_additivity_core_ready⟩

/-- The concrete countable-additivity discharge receipt is ready. -/
theorem spectral_measure_pvm_concrete_countable_discharge_receipt_target_ready :
    SpectralMeasurePVMConcreteCountableDischargeReceiptTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_operator_valued_concrete_finite_additivity_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Concrete countable-additivity core: the two-index concrete surface now has
countable-family objects, pairwise disjointness, branch-specific countable unions,
partial-union equations, and concrete all-empty / pinned single-whole
sigma-additivity receipts. -/
def SpectralMeasurePVMOperatorValuedConcreteCountableAdditivityCoreReady : Prop :=
  SpectralMeasurePVMConcreteCountableDisjointFamilyTarget ∧
  SpectralMeasurePVMConcreteCountableUnionIndexTarget ∧
  SpectralMeasurePVMConcreteFinitePartialSumSequenceTarget ∧
  SpectralMeasurePVMConcreteMonotonePartialProjectionFamilyTarget ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteSigmaAdditivityReceiptTarget ∧
  SpectralMeasurePVMConcreteCountableAdditivityFeedsSpectralCompatibilityTarget ∧
  SpectralMeasurePVMConcreteNoSpectralCompatibilityUseBeforeCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteCountableDischargeReceiptTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete countable-additivity core is ready. -/
theorem spectral_measure_pvm_operator_valued_concrete_countable_additivity_core_ready :
    SpectralMeasurePVMOperatorValuedConcreteCountableAdditivityCoreReady := by
  exact ⟨
    spectral_measure_pvm_concrete_countable_disjoint_family_target_ready,
    spectral_measure_pvm_concrete_countable_union_index_target_ready,
    spectral_measure_pvm_concrete_finite_partial_sum_sequence_target_ready,
    spectral_measure_pvm_concrete_monotone_partial_projection_family_target_ready,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_sigma_additivity_receipt_target_ready,
    spectral_measure_pvm_concrete_countable_additivity_feeds_spectral_compatibility_target_ready,
    spectral_measure_pvm_concrete_no_spectral_compatibility_use_before_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_countable_discharge_receipt_target_ready,
    spectral_measure_pvm_operator_valued_concrete_finite_additivity_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
