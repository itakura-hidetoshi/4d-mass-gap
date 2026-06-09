import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
import MGAP4D.HardPhysicalResidualLedgerR3ToR4PreSpectralHandoff

namespace MGAP4D

/-- R3 theorem-discharge packet for the two formerly named hard points.

This layer consumes the theorem surfaces:

* `concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem`;
* `concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem`.

It does not automatically open R4--R7.  It only replaces the two R3 named
obligation markers by proof-carrying theorem surfaces, preserving final-release
hold and public-boundary lock. -/
structure HardPhysicalResidualLedgerR3TheoremDischarge where
  preSpectralHandoffReady : hardPhysicalResidualLedgerR3ToR4PreSpectralHandoff3320.ready
  mathlibAdjointGraphTheorem :
    ∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W
  canonicalMathlibAdjointGraphTheorem :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness
  concreteSelfAdjointnessTheorem :
    ∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W
  canonicalConcreteSelfAdjointnessTheorem :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness
  r3AfterConcreteSelfAdjointnessReady :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3AfterConcreteSelfAdjointnessTheorem
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  r4ConcretePVMStillDownstream : hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream
  r5PlaquetteObservableStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream
  r6NondefinitionalAtomStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream
  r7PositiveWeightStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Readiness predicate for the R3 theorem-discharge packet.

The predicate is expressed in terms of the underlying proposition anchors, not the
proof-term fields of a particular packet.  This avoids using a proof object as a
proposition type in the final conjunction. -/
def HardPhysicalResidualLedgerR3TheoremDischarge.ready
    (_D : HardPhysicalResidualLedgerR3TheoremDischarge) : Prop :=
  hardPhysicalResidualLedgerR3ToR4PreSpectralHandoff3320.ready ∧
  (∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
  (∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W) ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3AfterConcreteSelfAdjointnessTheorem ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Canonical theorem-discharge packet for R3. -/
def hardPhysicalResidualLedgerR3TheoremDischarge3320 :
    HardPhysicalResidualLedgerR3TheoremDischarge :=
  { preSpectralHandoffReady :=
      hard_physical_residual_ledger_r3_to_r4_pre_spectral_handoff_3320_ready
    mathlibAdjointGraphTheorem :=
      MathlibAnalytic.concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_ready
    canonicalMathlibAdjointGraphTheorem :=
      MathlibAnalytic.concrete_analytic_spine_hard_residual_r3_canonical_mathlib_adjoint_graph_theorem_ready
    concreteSelfAdjointnessTheorem :=
      MathlibAnalytic.concrete_analytic_spine_hard_residual_r3_concrete_self_adjointness_theorem_ready
    canonicalConcreteSelfAdjointnessTheorem :=
      MathlibAnalytic.concrete_analytic_spine_hard_residual_r3_canonical_concrete_self_adjointness_theorem_ready
    r3AfterConcreteSelfAdjointnessReady :=
      MathlibAnalytic.concrete_analytic_spine_hard_residual_r3_after_concrete_self_adjointness_theorem_ready
    finalReleaseHeld :=
      hard_physical_residual_ledger_r3_to_r4_pre_spectral_handoff_final_release_held
    publicBoundaryLocked :=
      hard_physical_residual_ledger_r3_to_r4_pre_spectral_handoff_public_boundary_locked
    r4ConcretePVMStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream_proof
    r5PlaquetteObservableStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream_proof
    r6NondefinitionalAtomStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream_proof
    r7PositiveWeightStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream_proof }

/-- The canonical R3 theorem-discharge packet is ready. -/
theorem hard_physical_residual_ledger_r3_theorem_discharge_3320_ready :
    hardPhysicalResidualLedgerR3TheoremDischarge3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischarge3320.preSpectralHandoffReady,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.mathlibAdjointGraphTheorem,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.canonicalMathlibAdjointGraphTheorem,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.concreteSelfAdjointnessTheorem,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.canonicalConcreteSelfAdjointnessTheorem,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r3AfterConcreteSelfAdjointnessReady,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r4ConcretePVMStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r5PlaquetteObservableStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r7PositiveWeightStillDownstream⟩

/-- Projection: first named R3 hard point is theorem-discharge ready. -/
theorem hard_physical_residual_ledger_r3_theorem_discharge_mathlib_adjoint_graph_theorem :
    ∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W := by
  exact hardPhysicalResidualLedgerR3TheoremDischarge3320.mathlibAdjointGraphTheorem

/-- Projection: second named R3 hard point is theorem-discharge ready. -/
theorem hard_physical_residual_ledger_r3_theorem_discharge_concrete_self_adjointness_theorem :
    ∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W := by
  exact hardPhysicalResidualLedgerR3TheoremDischarge3320.concreteSelfAdjointnessTheorem

/-- Projection: the canonical witness has both R3 theorem discharges. -/
theorem hard_physical_residual_ledger_r3_theorem_discharge_canonical_pair :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischarge3320.canonicalMathlibAdjointGraphTheorem,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.canonicalConcreteSelfAdjointnessTheorem⟩

/-- Projection: R4--R7 remain downstream after R3 theorem discharge. -/
theorem hard_physical_residual_ledger_r3_theorem_discharge_r4_r7_downstream_visible :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r4ConcretePVMStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r5PlaquetteObservableStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischarge3320.r7PositiveWeightStillDownstream⟩

end MGAP4D
