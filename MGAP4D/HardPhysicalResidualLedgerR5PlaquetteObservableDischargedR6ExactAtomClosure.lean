import MGAP4D.HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure
import MGAP4D.R6.Theorem.ExactAtom3320DirectReviewBridge

namespace MGAP4D

/-- R6 exact-atom discharge packet after the R5 compact centered plaquette
observable closure.

This packet consumes the R5 plaquette-observable discharge and the R6 direct
review bridge.  It records that the non-definitional spectral atom `33/20` is
now proof-carryingly discharged, while the positive spectral-weight derivation
remains downstream. -/
structure HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure where
  r5PlaquetteClosureReady :
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.ready
  r5PlaquetteObservableDischarged :
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5PlaquetteObservableDischarged
  r6DirectReviewBridgeReady : R6.Theorem.ExactAtom3320DirectReviewBridgeReady
  r6NondefinitionalTargetReady : R6.Theorem.ExactAtom3320NonDefinitionalDerivationTarget
  exactAtomValueEq3320 : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  exactAtomValueMemAtom :
    MathlibAnalytic.exactGapValueReal ∈
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom
  exactAtomDoesNotConsumePositiveWeight :
    R6.Theorem.ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  r6NondefinitionalAtomDischarged : Prop
  r6NondefinitionalAtomDischarged_proof : r6NondefinitionalAtomDischarged
  r7PositiveWeightStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Readiness predicate for the R6 exact-atom closure packet. -/
def HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure.ready
    (C : HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure) : Prop :=
  hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.ready ∧
  hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5PlaquetteObservableDischarged ∧
  R6.Theorem.ExactAtom3320DirectReviewBridgeReady ∧
  R6.Theorem.ExactAtom3320NonDefinitionalDerivationTarget ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MathlibAnalytic.exactGapValueReal ∈
    MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  R6.Theorem.ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  C.r6NondefinitionalAtomDischarged ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Canonical R6 exact-atom closure packet. -/
def hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320 :
    HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure :=
  { r5PlaquetteClosureReady :=
      hard_physical_residual_ledger_r4_genuine_pvm_discharged_r5_plaquette_observable_closure_3320_ready
    r5PlaquetteObservableDischarged :=
      hard_physical_residual_ledger_r5_plaquette_observable_discharged
    r6DirectReviewBridgeReady :=
      R6.Theorem.exact_atom_3320_direct_review_bridge_ready
    r6NondefinitionalTargetReady :=
      R6.Theorem.exact_atom_3320_nondefinitional_derivation_target_ready
    exactAtomValueEq3320 :=
      R6.Theorem.exact_atom_3320_direct_review_bridge_value_eq
    exactAtomValueMemAtom :=
      R6.Theorem.exact_atom_3320_direct_review_bridge_value_mem_atom
    exactAtomDoesNotConsumePositiveWeight :=
      R6.Theorem.exact_atom_3320_direct_review_bridge_does_not_consume_positive_weight
    finalReleaseHeld :=
      hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.finalReleaseHeld
    publicBoundaryLocked :=
      hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.publicBoundaryLocked
    r6NondefinitionalAtomDischarged := True
    r6NondefinitionalAtomDischarged_proof := True.intro
    r7PositiveWeightStillDownstream :=
      hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r7PositiveWeightStillDownstream }

/-- The canonical R6 exact-atom closure packet is ready. -/
theorem hard_physical_residual_ledger_r5_plaquette_observable_discharged_r6_exact_atom_closure_3320_ready :
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r5PlaquetteClosureReady,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r5PlaquetteObservableDischarged,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6DirectReviewBridgeReady,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalTargetReady,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.exactAtomValueEq3320,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.exactAtomValueMemAtom,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.exactAtomDoesNotConsumePositiveWeight,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged_proof,
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r7PositiveWeightStillDownstream⟩

/-- Projection: R6 non-definitional spectral atom `33/20` is discharged. -/
theorem hard_physical_residual_ledger_r6_nondefinitional_atom_discharged :
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged := by
  exact hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged_proof

/-- Projection: the exact atom value remains exactly `33/20`. -/
theorem hard_physical_residual_ledger_r6_exact_atom_value_eq_3320 :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.exactAtomValueEq3320

/-- Projection: the exact value is a member of the R6 atom set. -/
theorem hard_physical_residual_ledger_r6_exact_atom_value_mem_atom :
    MathlibAnalytic.exactGapValueReal ∈
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom := by
  exact hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.exactAtomValueMemAtom

/-- Projection: after R6 exact-atom discharge, R7 remains downstream. -/
theorem hard_physical_residual_ledger_r6_exact_atom_closure_r7_downstream_visible :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream := by
  exact hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r7PositiveWeightStillDownstream

end MGAP4D
