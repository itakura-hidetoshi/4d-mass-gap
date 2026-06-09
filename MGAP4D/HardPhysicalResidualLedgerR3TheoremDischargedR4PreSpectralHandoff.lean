import MGAP4D.HardPhysicalResidualLedgerR3TheoremDischarge
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelPreSelfAdjointSpectralTheoremHandoff

namespace MGAP4D

/-- R3 theorem-discharged bridge into the R4 pre-spectral surface.

This packet is the post-R3 version of the earlier pre-spectral handoff: the two
R3 hard points are consumed as theorem surfaces, while the actual R4 spectral
measure construction is still downstream.  In particular, this bridge does not
turn the actual-Borel pre-spectral receiver into a genuine PVM. -/
structure HardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff where
  r3TheoremDischargeReady : hardPhysicalResidualLedgerR3TheoremDischarge3320.ready
  mathlibAdjointGraphTheorem :
    ∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W
  concreteSelfAdjointnessTheorem :
    ∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W
  r4PreSpectralHandoffReady :
    R4.Theorem.SpectralMeasurePVMActualBorelPreSelfAdjointSpectralTheoremHandoffBridgeReady
  r4PreSpectralPublicBoundaryHeld :
    R4.Theorem.SpectralMeasurePVMActualBorelPreSelfAdjointSpectralTheoremHandoffPublicBoundaryHeld
  r4GenuineSelfAdjointSpectralTheoremStillOpen :
    R4.Theorem.SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen
  r4GenuineSpectralMeasureConstructionStillOpen :
    R4.Theorem.SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
  r4NoShellCollapse : R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  r4PromotionBlockedUntilR4SpectralTheorem : Prop
  r4PromotionBlockedUntilR4SpectralTheorem_proof :
    r4PromotionBlockedUntilR4SpectralTheorem
  r4ConcretePVMStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream
  r5PlaquetteObservableStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream
  r6NondefinitionalAtomStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream
  r7PositiveWeightStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Readiness predicate for the post-R3 theorem-discharged R4 pre-spectral bridge.

The proposition intentionally names the theorem-discharge surfaces and the R4
open-boundary surfaces separately.  This prevents a silent promotion from
"R3 self-adjointness theorem surfaces are available" to "R4 PVM is built". -/
def HardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff.ready
    (H : HardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff) : Prop :=
  hardPhysicalResidualLedgerR3TheoremDischarge3320.ready ∧
  (∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) ∧
  (∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W) ∧
  R4.Theorem.SpectralMeasurePVMActualBorelPreSelfAdjointSpectralTheoremHandoffBridgeReady ∧
  R4.Theorem.SpectralMeasurePVMActualBorelPreSelfAdjointSpectralTheoremHandoffPublicBoundaryHeld ∧
  R4.Theorem.SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  R4.Theorem.SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  H.r4PromotionBlockedUntilR4SpectralTheorem ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream

/-- Canonical post-R3 theorem-discharged R4 pre-spectral handoff. -/
def hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320 :
    HardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff :=
  { r3TheoremDischargeReady :=
      hard_physical_residual_ledger_r3_theorem_discharge_3320_ready
    mathlibAdjointGraphTheorem :=
      hard_physical_residual_ledger_r3_theorem_discharge_mathlib_adjoint_graph_theorem
    concreteSelfAdjointnessTheorem :=
      hard_physical_residual_ledger_r3_theorem_discharge_concrete_self_adjointness_theorem
    r4PreSpectralHandoffReady :=
      R4.Theorem.spectral_measure_pvm_actual_borel_pre_self_adjoint_spectral_theorem_handoff_bridge_ready
    r4PreSpectralPublicBoundaryHeld :=
      R4.Theorem.spectral_measure_pvm_actual_borel_pre_self_adjoint_spectral_theorem_handoff_public_boundary_held
    r4GenuineSelfAdjointSpectralTheoremStillOpen :=
      R4.Theorem.spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready
    r4GenuineSpectralMeasureConstructionStillOpen :=
      R4.Theorem.spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready
    r4NoShellCollapse :=
      R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready
    finalReleaseHeld :=
      hard_physical_residual_ledger_r3_to_r4_pre_spectral_handoff_final_release_held
    publicBoundaryLocked :=
      hard_physical_residual_ledger_r3_to_r4_pre_spectral_handoff_public_boundary_locked
    r4PromotionBlockedUntilR4SpectralTheorem := True
    r4PromotionBlockedUntilR4SpectralTheorem_proof := True.intro
    r4ConcretePVMStillDownstream :=
      hardPhysicalResidualLedgerR3TheoremDischarge3320.r4ConcretePVMStillDownstream
    r5PlaquetteObservableStillDownstream :=
      hardPhysicalResidualLedgerR3TheoremDischarge3320.r5PlaquetteObservableStillDownstream
    r6NondefinitionalAtomStillDownstream :=
      hardPhysicalResidualLedgerR3TheoremDischarge3320.r6NondefinitionalAtomStillDownstream
    r7PositiveWeightStillDownstream :=
      hardPhysicalResidualLedgerR3TheoremDischarge3320.r7PositiveWeightStillDownstream }

/-- The canonical post-R3 theorem-discharged R4 pre-spectral bridge is ready. -/
theorem hard_physical_residual_ledger_r3_theorem_discharged_r4_pre_spectral_handoff_3320_ready :
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r3TheoremDischargeReady,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.mathlibAdjointGraphTheorem,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.concreteSelfAdjointnessTheorem,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4PreSpectralHandoffReady,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4PreSpectralPublicBoundaryHeld,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4GenuineSelfAdjointSpectralTheoremStillOpen,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4GenuineSpectralMeasureConstructionStillOpen,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4NoShellCollapse,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4PromotionBlockedUntilR4SpectralTheorem_proof,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4ConcretePVMStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r5PlaquetteObservableStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r7PositiveWeightStillDownstream⟩

/-- Projection: the two R3 theorem surfaces are available for downstream R4 work. -/
theorem hard_physical_residual_ledger_r3_theorem_discharged_r4_pre_spectral_handoff_r3_theorems :
    (∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) ∧
    (∀ W : MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
      MathlibAnalytic.concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W) := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.mathlibAdjointGraphTheorem,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.concreteSelfAdjointnessTheorem⟩

/-- Projection: R4 is visible but remains pre-spectral, not a constructed PVM. -/
theorem hard_physical_residual_ledger_r3_theorem_discharged_r4_pre_spectral_handoff_r4_open_boundary :
    R4.Theorem.SpectralMeasurePVMActualBorelPreSelfAdjointSpectralTheoremHandoffBridgeReady ∧
      R4.Theorem.SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
      R4.Theorem.SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
      R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4PreSpectralHandoffReady,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4GenuineSelfAdjointSpectralTheoremStillOpen,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4GenuineSpectralMeasureConstructionStillOpen,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4NoShellCollapse⟩

/-- Projection: R4--R7 downstream visibility is preserved after R3 theorem discharge. -/
theorem hard_physical_residual_ledger_r3_theorem_discharged_r4_pre_spectral_handoff_downstream_visible :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream := by
  exact ⟨
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r4ConcretePVMStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r5PlaquetteObservableStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR3TheoremDischargedR4PreSpectralHandoff3320.r7PositiveWeightStillDownstream⟩

end MGAP4D
