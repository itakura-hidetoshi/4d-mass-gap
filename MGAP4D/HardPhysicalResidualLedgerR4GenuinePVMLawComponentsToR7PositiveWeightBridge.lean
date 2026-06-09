import MGAP4D.HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR6ExactAtomBridge
import MGAP4D.HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure

namespace MGAP4D

/-- Bridge from R4 genuine-PVM law receipts through R6 exact atom closure to the
R7 positive spectral-weight witness.

The purpose is narrow: keep the genuine PVM laws visible at the terminal
positive-weight closure point.  It does not weaken the public/final boundary and
it does not introduce a new release authority. -/
structure HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge where
  r4ToR6BridgeReady :
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR6ExactAtomBridge3320.ready
  r7PositiveWeightClosureReady :
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.ready
  r4CountableAdditivityVisibleAtR7 :
    R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem
  r4NoShellBoundaryVisibleAtR7 :
    R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary
  r6ExactAtomDischarged :
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged
  r7PositiveWeightDischarged :
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightDischarged
  exactValueEq3320 : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  exactValueMemAtom :
    MathlibAnalytic.exactGapValueReal ∈
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom
  positiveMassProof :
    Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
  positiveWeightOrthogonalNonvacuum :
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
        Spectral.SpectralSector.orthogonal ∧
      Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
        Spectral.SpectralSector.vacuum
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  r4LawComponentsBridgeToR7 : Prop
  r4LawComponentsBridgeToR7_proof : r4LawComponentsBridgeToR7

/-- Readiness predicate for the R4-law-components to R7-positive-weight bridge. -/
def HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge.ready
    (B : HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge) : Prop :=
  hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR6ExactAtomBridge3320.ready ∧
  hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.ready ∧
  R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
  R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary ∧
  hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged ∧
  hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightDischarged ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MathlibAnalytic.exactGapValueReal ∈
    MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  (Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal ∧
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum) ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  B.r4LawComponentsBridgeToR7

/-- Canonical bridge from R4 genuine-PVM law components to the R7 positive
spectral-weight witness. -/
def hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320 :
    HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge :=
  { r4ToR6BridgeReady :=
      hard_physical_residual_ledger_r4_genuine_pvm_law_components_to_r6_exact_atom_bridge_3320_ready
    r7PositiveWeightClosureReady :=
      hard_physical_residual_ledger_r6_exact_atom_discharged_r7_positive_weight_closure_3320_ready
    r4CountableAdditivityVisibleAtR7 :=
      hard_physical_residual_ledger_r4_genuine_pvm_countable_additivity_visible_at_r6
    r4NoShellBoundaryVisibleAtR7 :=
      hard_physical_residual_ledger_r6_exact_atom_keeps_r4_no_shell_boundary
    r6ExactAtomDischarged :=
      hard_physical_residual_ledger_r6_nondefinitional_atom_discharged
    r7PositiveWeightDischarged :=
      hard_physical_residual_ledger_r7_positive_weight_discharged
    exactValueEq3320 :=
      hard_physical_residual_ledger_r7_positive_weight_exact_value_eq_3320
    exactValueMemAtom :=
      hard_physical_residual_ledger_r7_positive_weight_exact_value_mem_atom
    positiveMassProof :=
      hard_physical_residual_ledger_r7_positive_weight_positive_mass
    positiveWeightOrthogonalNonvacuum :=
      hard_physical_residual_ledger_r7_positive_weight_orthogonal_nonvacuum
    finalReleaseHeld :=
      hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.finalReleaseHeld
    publicBoundaryLocked :=
      hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.publicBoundaryLocked
    r4LawComponentsBridgeToR7 := True
    r4LawComponentsBridgeToR7_proof := True.intro }

/-- The canonical R4-law-components to R7-positive-weight bridge is ready. -/
theorem hard_physical_residual_ledger_r4_genuine_pvm_law_components_to_r7_positive_weight_bridge_3320_ready :
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r4ToR6BridgeReady,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r7PositiveWeightClosureReady,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r4CountableAdditivityVisibleAtR7,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r4NoShellBoundaryVisibleAtR7,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r6ExactAtomDischarged,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r7PositiveWeightDischarged,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.exactValueEq3320,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.exactValueMemAtom,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.positiveMassProof,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.positiveWeightOrthogonalNonvacuum,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r4LawComponentsBridgeToR7_proof⟩

/-- Projection: at R7, the terminal positive-weight witness still carries the R4
operator-topology countable-additivity receipt. -/
theorem hard_physical_residual_ledger_r7_positive_weight_carries_r4_countable_additivity :
    R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem := by
  exact hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.r4CountableAdditivityVisibleAtR7

/-- Projection: at R7, the exact `33/20` atom and positive-weight witness are
jointly visible. -/
theorem hard_physical_residual_ledger_r7_exact_atom_and_positive_weight_joint_visible :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      MathlibAnalytic.exactGapValueReal ∈
        MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  exact ⟨
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.exactValueEq3320,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.exactValueMemAtom,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.positiveMassProof⟩

/-- Projection: even after the R4-law-component to R7 bridge, public/final
boundaries remain locked. -/
theorem hard_physical_residual_ledger_r4_laws_to_r7_boundary_locked :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
      r1r7TheoremObligationCompletion3320.publicBoundaryLocked := by
  exact ⟨
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge3320.publicBoundaryLocked⟩

end MGAP4D
