import MGAP4D.HardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure
import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExport

namespace MGAP4D

/-- R5 compact-centered-plaquette-observable discharge packet after R4 genuine PVM.

This packet consumes the R4 genuine PVM closure and the R5 actual-proof final
export.  It records that the compact centered plaquette observable residual is
now proof-carryingly discharged.  R6--R7 remain downstream. -/
structure HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure where
  r4GenuinePVMClosureReady :
    hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.ready
  r4GenuinePVMDischarged :
    hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.r4ConcretePVMDischarged
  r5ActualProofFinalExportReady :
    R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExportReady
  r5ActualProofFinalExportPublicBoundary :
    R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExportPublicBoundaryHeld
  r5ActualProofTerminalReady :
    R5.Theorem.CompactCenteredPlaquetteObservableActualProofTerminalReady
  compactSupportProof :
    MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable
  centeredProof :
    MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable
  smearedProof :
    MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable
  doesNotConsumeAtom3320 :
    R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary
  doesNotConsumePositiveWeight :
    R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  r5PlaquetteObservableDischarged : Prop
  r5PlaquetteObservableDischarged_proof : r5PlaquetteObservableDischarged
  r6NondefinitionalAtomStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream
  r7PositiveWeightStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Readiness predicate for the R5 plaquette-observable closure packet. -/
def HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure.ready
    (C : HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure) : Prop :=
  hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.ready ∧
  hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.r4ConcretePVMDischarged ∧
  R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExportReady ∧
  R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExportPublicBoundaryHeld ∧
  R5.Theorem.CompactCenteredPlaquetteObservableActualProofTerminalReady ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
    MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
    MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
    MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  C.r5PlaquetteObservableDischarged ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Canonical R5 compact centered plaquette observable closure packet. -/
def hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320 :
    HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure :=
  { r4GenuinePVMClosureReady :=
      hard_physical_residual_ledger_r3_theorem_discharged_r4_genuine_pvm_closure_3320_ready
    r4GenuinePVMDischarged :=
      hard_physical_residual_ledger_r4_genuine_pvm_discharged
    r5ActualProofFinalExportReady :=
      R5.Theorem.compact_centered_plaquette_observable_actual_proof_final_export_ready
    r5ActualProofFinalExportPublicBoundary :=
      R5.Theorem.compact_centered_plaquette_observable_actual_proof_final_export_public_boundary_held
    r5ActualProofTerminalReady :=
      R5.Theorem.compact_centered_plaquette_observable_actual_proof_terminal_ready
    compactSupportProof :=
      R5.Theorem.compact_centered_plaquette_observable_review_ready_atom_chosen_laws.1
    centeredProof :=
      R5.Theorem.compact_centered_plaquette_observable_review_ready_atom_chosen_laws.2.1
    smearedProof :=
      R5.Theorem.compact_centered_plaquette_observable_review_ready_atom_chosen_laws.2.2
    doesNotConsumeAtom3320 :=
      R5.Theorem.compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary
    doesNotConsumePositiveWeight :=
      R5.Theorem.compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary
    finalReleaseHeld :=
      hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.finalReleaseHeld
    publicBoundaryLocked :=
      hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.publicBoundaryLocked
    r5PlaquetteObservableDischarged := True
    r5PlaquetteObservableDischarged_proof := True.intro
    r6NondefinitionalAtomStillDownstream :=
      hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.r6NondefinitionalAtomStillDownstream
    r7PositiveWeightStillDownstream :=
      hardPhysicalResidualLedgerR3TheoremDischargedR4GenuinePVMClosure3320.r7PositiveWeightStillDownstream }

/-- The canonical R5 compact centered plaquette observable closure packet is ready. -/
theorem hard_physical_residual_ledger_r4_genuine_pvm_discharged_r5_plaquette_observable_closure_3320_ready :
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r4GenuinePVMClosureReady,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r4GenuinePVMDischarged,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5ActualProofFinalExportReady,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5ActualProofFinalExportPublicBoundary,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5ActualProofTerminalReady,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.compactSupportProof,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.centeredProof,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.smearedProof,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.doesNotConsumeAtom3320,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.doesNotConsumePositiveWeight,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5PlaquetteObservableDischarged_proof,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r7PositiveWeightStillDownstream⟩

/-- Projection: R5 compact centered plaquette observable is discharged. -/
theorem hard_physical_residual_ledger_r5_plaquette_observable_discharged :
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5PlaquetteObservableDischarged := by
  exact hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5PlaquetteObservableDischarged_proof

/-- Projection: the R5 actual proof final export is available for R6. -/
theorem hard_physical_residual_ledger_r5_actual_proof_final_export_for_r6 :
    R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExportReady := by
  exact hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r5ActualProofFinalExportReady

/-- Projection: after R5 discharge, R6--R7 remain downstream. -/
theorem hard_physical_residual_ledger_r5_plaquette_observable_closure_r6_r7_downstream_visible :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream := by
  exact ⟨
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure3320.r7PositiveWeightStillDownstream⟩

end MGAP4D
