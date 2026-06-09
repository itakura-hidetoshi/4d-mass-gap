import MGAP4D.HardPhysicalResidualLedgerR3ClosureObligationMap

namespace MGAP4D

/-- Stable chain index for the R3 closure-obligation map.

This is deliberately an index, not a closure theorem.  It keeps the two named R3
hard points importable from one root:

* the Mathlib adjoint-graph theorem;
* the resulting concrete self-adjointness theorem.

R4--R7 remain downstream until those R3 obligations are replaced by stronger
Mathlib/operator-theoretic proofs. -/
structure HardPhysicalResidualLedgerR3ClosureObligationMapChainIndex where
  closureObligationMapReady : hardPhysicalResidualLedgerR3ClosureObligationMap3320.ready
  inputBridgeReady : hardPhysicalResidualLedgerR3SelfAdjointInputBridge3320.ready
  adjointTransportReady :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3MathlibAdjointTransportTargetReady
  adjointGraphContractReady :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3MathlibAdjointGraphContractReady
  missingSelfAdjointVisible :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3MissingSelfAdjointTheorem
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  mathlibAdjointGraphTheoremObligation :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.mathlibAdjointGraphTheoremObligation
  concreteSelfAdjointTheoremObligation :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.concreteSelfAdjointTheoremObligation
  r4ConcretePVMStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream
  r5PlaquetteObservableStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream
  r6NondefinitionalAtomStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream
  r7PositiveWeightStillDownstream :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream
  chainIndexVisible : Prop
  chainIndexVisible_proof : chainIndexVisible

/-- Readiness predicate for the R3 closure-obligation chain index.

The predicate uses the underlying proposition anchors, avoiding proof-term fields
as proposition types. -/
def HardPhysicalResidualLedgerR3ClosureObligationMapChainIndex.ready
    (I : HardPhysicalResidualLedgerR3ClosureObligationMapChainIndex) : Prop :=
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.ready ∧
  hardPhysicalResidualLedgerR3SelfAdjointInputBridge3320.ready ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3MathlibAdjointTransportTargetReady ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3MathlibAdjointGraphContractReady ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3MissingSelfAdjointTheorem ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.mathlibAdjointGraphTheoremObligation ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.concreteSelfAdjointTheoremObligation ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
  hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream ∧
  I.chainIndexVisible

/-- Canonical R3 closure-obligation map chain index. -/
def hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320 :
    HardPhysicalResidualLedgerR3ClosureObligationMapChainIndex :=
  { closureObligationMapReady :=
      hard_physical_residual_ledger_r3_closure_obligation_map_3320_ready
    inputBridgeReady :=
      hard_physical_residual_ledger_r3_closure_obligation_map_input_bridge_ready
    adjointTransportReady :=
      hard_physical_residual_ledger_r3_closure_obligation_map_adjoint_transport_ready
    adjointGraphContractReady :=
      hard_physical_residual_ledger_r3_closure_obligation_map_adjoint_graph_contract_ready
    missingSelfAdjointVisible :=
      hard_physical_residual_ledger_r3_closure_obligation_map_missing_self_adjoint_visible
    finalReleaseHeld :=
      hard_physical_residual_ledger_r3_closure_obligation_map_final_release_held
    publicBoundaryLocked :=
      hard_physical_residual_ledger_r3_closure_obligation_map_public_boundary_locked
    mathlibAdjointGraphTheoremObligation :=
      hard_physical_residual_ledger_r3_closure_obligation_map_mathlib_adjoint_graph_obligation
    concreteSelfAdjointTheoremObligation :=
      hard_physical_residual_ledger_r3_closure_obligation_map_concrete_self_adjoint_obligation
    r4ConcretePVMStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream_proof
    r5PlaquetteObservableStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream_proof
    r6NondefinitionalAtomStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream_proof
    r7PositiveWeightStillDownstream :=
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream_proof
    chainIndexVisible := True
    chainIndexVisible_proof := True.intro }

/-- The canonical R3 closure-obligation chain index is ready. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_3320_ready :
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.closureObligationMapReady,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.inputBridgeReady,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.adjointTransportReady,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.adjointGraphContractReady,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.missingSelfAdjointVisible,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.mathlibAdjointGraphTheoremObligation,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.concreteSelfAdjointTheoremObligation,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r4ConcretePVMStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r5PlaquetteObservableStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r7PositiveWeightStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.chainIndexVisible_proof⟩

/-- Projection: the chain index carries the R3 closure-obligation map. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_map_ready :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.ready := by
  exact hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.closureObligationMapReady

/-- Projection: the chain index preserves the Mathlib adjoint-graph hard point. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_mathlib_adjoint_graph_obligation :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.mathlibAdjointGraphTheoremObligation := by
  exact hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.mathlibAdjointGraphTheoremObligation

/-- Projection: the chain index preserves the concrete self-adjointness hard point. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_concrete_self_adjoint_obligation :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.concreteSelfAdjointTheoremObligation := by
  exact hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.concreteSelfAdjointTheoremObligation

/-- Projection: R4--R7 remain downstream of actual R3 closure. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_r4_r7_downstream_visible :
    hardPhysicalResidualLedgerR3ClosureObligationMap3320.r4ConcretePVMStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r5PlaquetteObservableStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r6NondefinitionalAtomStillDownstream ∧
      hardPhysicalResidualLedgerR3ClosureObligationMap3320.r7PositiveWeightStillDownstream := by
  exact ⟨
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r4ConcretePVMStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r5PlaquetteObservableStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r6NondefinitionalAtomStillDownstream,
    hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.r7PositiveWeightStillDownstream⟩

/-- Projection: the final-release boundary remains held at the R3 chain index. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_final_release_held :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld := by
  exact hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.finalReleaseHeld

/-- Projection: the public boundary remains locked at the R3 chain index. -/
theorem hard_physical_residual_ledger_r3_closure_obligation_map_chain_index_public_boundary_locked :
    r1r7TheoremObligationCompletion3320.publicBoundaryLocked := by
  exact hardPhysicalResidualLedgerR3ClosureObligationMapChainIndex3320.publicBoundaryLocked

end MGAP4D
