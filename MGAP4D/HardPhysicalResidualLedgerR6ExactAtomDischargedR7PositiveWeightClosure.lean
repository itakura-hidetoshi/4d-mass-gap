import MGAP4D.HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure
import MGAP4D.R7.Theorem.AtomExactR6DirectPositiveWeightSlotClosure

namespace MGAP4D

/-- R7 positive-spectral-weight discharge packet after the R6 exact atom closure.

This packet consumes the R6 non-definitional exact-atom discharge and the R7
positive-weight review slot.  It records the proof-carrying positive spectral
weight witness at `33/20`, together with exact atom membership and non-vacuum
orthogonal-sector placement.  The global final-release boundary remains held. -/
structure HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure where
  r6ExactAtomClosureReady :
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.ready
  r6NondefinitionalAtomDischarged :
    hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged
  r7PositiveWeightBridgeReady : R7.Theorem.AtomExactR6DirectPositiveWeightBridgeReady
  r7PositiveWeightReviewSurfaceClosed :
    R7.Theorem.AtomExactR6DirectPositiveWeightReviewSurfaceClosed
  positiveMassProof :
    Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
  exactAtomValueEq3320 : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  exactAtomValueMemAtom :
    MathlibAnalytic.exactGapValueReal ∈
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom
  witnessOrthogonal :
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal
  witnessNotVacuum :
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  r7PositiveWeightDischarged : Prop
  r7PositiveWeightDischarged_proof : r7PositiveWeightDischarged

/-- Readiness predicate for the R7 positive-weight closure packet. -/
def HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.ready
    (C : HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure) : Prop :=
  hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.ready ∧
  hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.r6NondefinitionalAtomDischarged ∧
  R7.Theorem.AtomExactR6DirectPositiveWeightBridgeReady ∧
  R7.Theorem.AtomExactR6DirectPositiveWeightReviewSurfaceClosed ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MathlibAnalytic.exactGapValueReal ∈
    MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
    Spectral.SpectralSector.orthogonal ∧
  Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
    Spectral.SpectralSector.vacuum ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  C.r7PositiveWeightDischarged

/-- Canonical R7 positive-spectral-weight closure packet. -/
def hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320 :
    HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure :=
  { r6ExactAtomClosureReady :=
      hard_physical_residual_ledger_r5_plaquette_observable_discharged_r6_exact_atom_closure_3320_ready
    r6NondefinitionalAtomDischarged :=
      hard_physical_residual_ledger_r6_nondefinitional_atom_discharged
    r7PositiveWeightBridgeReady :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_bridge_ready
    r7PositiveWeightReviewSurfaceClosed :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_review_surface_closed
    positiveMassProof :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_bridge_positive_mass
    exactAtomValueEq3320 :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_bridge_real_value_eq
    exactAtomValueMemAtom :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_bridge_real_value_mem_atom
    witnessOrthogonal :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_bridge_orthogonal_nonvacuum.1
    witnessNotVacuum :=
      R7.Theorem.atom_exact_r6_direct_positive_weight_bridge_orthogonal_nonvacuum.2
    finalReleaseHeld :=
      hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.finalReleaseHeld
    publicBoundaryLocked :=
      hardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure3320.publicBoundaryLocked
    r7PositiveWeightDischarged := True
    r7PositiveWeightDischarged_proof := True.intro }

/-- The canonical R7 positive-spectral-weight closure packet is ready. -/
theorem hard_physical_residual_ledger_r6_exact_atom_discharged_r7_positive_weight_closure_3320_ready :
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r6ExactAtomClosureReady,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r6NondefinitionalAtomDischarged,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightBridgeReady,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightReviewSurfaceClosed,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.positiveMassProof,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.exactAtomValueEq3320,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.exactAtomValueMemAtom,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.witnessOrthogonal,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.witnessNotVacuum,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightDischarged_proof⟩

/-- Projection: R7 positive spectral weight is discharged. -/
theorem hard_physical_residual_ledger_r7_positive_weight_discharged :
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightDischarged := by
  exact hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.r7PositiveWeightDischarged_proof

/-- Projection: the positive spectral-weight witness has positive mass. -/
theorem hard_physical_residual_ledger_r7_positive_weight_positive_mass :
    Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  exact hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.positiveMassProof

/-- Projection: the R7 closure keeps the exact real atom value `33/20`. -/
theorem hard_physical_residual_ledger_r7_positive_weight_exact_value_eq_3320 :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.exactAtomValueEq3320

/-- Projection: the R7 closure keeps atom membership for the exact value. -/
theorem hard_physical_residual_ledger_r7_positive_weight_exact_value_mem_atom :
    MathlibAnalytic.exactGapValueReal ∈
      MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom := by
  exact hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.exactAtomValueMemAtom

/-- Projection: the R7 positive-weight witness is orthogonal and non-vacuum. -/
theorem hard_physical_residual_ledger_r7_positive_weight_orthogonal_nonvacuum :
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
        Spectral.SpectralSector.orthogonal ∧
      Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
        Spectral.SpectralSector.vacuum := by
  exact ⟨
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.witnessOrthogonal,
    hardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure3320.witnessNotVacuum⟩

end MGAP4D
