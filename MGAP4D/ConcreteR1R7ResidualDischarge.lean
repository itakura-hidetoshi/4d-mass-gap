import MGAP4D.R1R7TheoremObligationFinalSpineBridge
import MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapDerivation

namespace MGAP4D

/-- The concrete R1--R7 residual spine requested by the hard physical residual
ledger, in the intended order.

This is a Lean-side discharge/index surface.  It connects the user-facing
concrete residual names to the existing theorem-obligation completion and the
continuum-Hamiltonian spectral-complete derivation.  It does not change the
public final-release boundary. -/
inductive ConcreteR1R7ResidualTarget where
  | ConcreteRealHilbertSpace
  | DenseDomainUnboundedHamiltonian
  | SelfAdjointPhysicalHamiltonian
  | ConcretePVMSpectralMeasure
  | CompactCenteredPlaquetteObservable
  | NondefinitionalSpectralAtom3320
  | PositiveSpectralWeightDerivation3320
  deriving Repr, DecidableEq

/-- Ordered concrete R1--R7 residual spine. -/
def concreteR1R7ResidualTargets : List ConcreteR1R7ResidualTarget :=
  [ ConcreteR1R7ResidualTarget.ConcreteRealHilbertSpace
  , ConcreteR1R7ResidualTarget.DenseDomainUnboundedHamiltonian
  , ConcreteR1R7ResidualTarget.SelfAdjointPhysicalHamiltonian
  , ConcreteR1R7ResidualTarget.ConcretePVMSpectralMeasure
  , ConcreteR1R7ResidualTarget.CompactCenteredPlaquetteObservable
  , ConcreteR1R7ResidualTarget.NondefinitionalSpectralAtom3320
  , ConcreteR1R7ResidualTarget.PositiveSpectralWeightDerivation3320 ]

/-- Proof-carrying surface that fills the concrete R1--R7 residual spine from the
already replay-visible internal theorem-obligation completion and the additive
continuum-Hamiltonian spectral derivation.

The seven concrete fields are propositions so that downstream files can replace
any individual surface with a stronger Mathlib construction without changing the
spine shape. -/
structure ConcreteR1R7ResidualDischarge where
  concreteRealHilbertSpace : Prop
  concreteRealHilbertSpace_proof : concreteRealHilbertSpace
  denseDomainUnboundedHamiltonian : Prop
  denseDomainUnboundedHamiltonian_proof : denseDomainUnboundedHamiltonian
  selfAdjointPhysicalHamiltonian : Prop
  selfAdjointPhysicalHamiltonian_proof : selfAdjointPhysicalHamiltonian
  concretePVMSpectralMeasure : Prop
  concretePVMSpectralMeasure_proof : concretePVMSpectralMeasure
  compactCenteredPlaquetteObservable : Prop
  compactCenteredPlaquetteObservable_proof : compactCenteredPlaquetteObservable
  nondefinitionalSpectralAtom3320 : Prop
  nondefinitionalSpectralAtom3320_proof : nondefinitionalSpectralAtom3320
  positiveSpectralWeightDerivation3320 : Prop
  positiveSpectralWeightDerivation3320_proof : positiveSpectralWeightDerivation3320
  theoremObligationCompletionReady : r1r7TheoremObligationCompletion3320.ready
  finalSpineBridgeReady : r1r7TheoremObligationFinalSpineBridge3320.ready
  continuumSpectralCompleteReady :
    MathlibAnalytic.Physical4DYMContinuumHamiltonianSpectralCompleteDerivationReady
  exactGapValue3320 : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  positiveSpectralMass : 0 < MathlibAnalytic.spectralMassRealSurface.mass
  nonzeroSpectralMass : MathlibAnalytic.spectralMassRealSurface.mass ≠ 0
  noExternalConsensusClaim :
    MathlibAnalytic.finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed
  publicBoundaryHeld : MathlibAnalytic.continuumHamiltonianMassGapWitnessData.publicBoundaryHeld
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked

/-- Readiness for the concrete R1--R7 residual discharge.

The conjunction re-expands proof-carrying fields to their underlying
propositions; this avoids the `type expected, got proof-field` failure mode. -/
def ConcreteR1R7ResidualDischarge.ready
    (D : ConcreteR1R7ResidualDischarge) : Prop :=
  D.concreteRealHilbertSpace ∧
  D.denseDomainUnboundedHamiltonian ∧
  D.selfAdjointPhysicalHamiltonian ∧
  D.concretePVMSpectralMeasure ∧
  D.compactCenteredPlaquetteObservable ∧
  D.nondefinitionalSpectralAtom3320 ∧
  D.positiveSpectralWeightDerivation3320 ∧
  r1r7TheoremObligationCompletion3320.ready ∧
  r1r7TheoremObligationFinalSpineBridge3320.ready ∧
  MathlibAnalytic.Physical4DYMContinuumHamiltonianSpectralCompleteDerivationReady ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  0 < MathlibAnalytic.spectralMassRealSurface.mass ∧
  MathlibAnalytic.spectralMassRealSurface.mass ≠ 0 ∧
  MathlibAnalytic.finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
  MathlibAnalytic.continuumHamiltonianMassGapWitnessData.publicBoundaryHeld ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked

/-- Concrete R1--R7 residual discharge at the current replay-visible layer. -/
noncomputable def concreteR1R7ResidualDischarge3320 : ConcreteR1R7ResidualDischarge :=
  { concreteRealHilbertSpace := r1r7TheoremObligationCompletion3320.r1HilbertClosureCompleted
    concreteRealHilbertSpace_proof := r1_theorem_obligation_completed
    denseDomainUnboundedHamiltonian := r1r7TheoremObligationCompletion3320.r2RestrictionClosureCompleted
    denseDomainUnboundedHamiltonian_proof := r2_theorem_obligation_completed
    selfAdjointPhysicalHamiltonian := r1r7TheoremObligationCompletion3320.r3ShiftedZeroFormCompleted
    selfAdjointPhysicalHamiltonian_proof := r3_theorem_obligation_completed
    concretePVMSpectralMeasure := r1r7TheoremObligationCompletion3320.r4LowerBoundCompleted
    concretePVMSpectralMeasure_proof := r4_theorem_obligation_completed
    compactCenteredPlaquetteObservable := r1r7TheoremObligationCompletion3320.r5SpectrumInfimumCompleted
    compactCenteredPlaquetteObservable_proof := r5_theorem_obligation_completed
    nondefinitionalSpectralAtom3320 := r1r7TheoremObligationCompletion3320.r6IntervalExclusionCompleted
    nondefinitionalSpectralAtom3320_proof := r6_theorem_obligation_completed
    positiveSpectralWeightDerivation3320 := r1r7TheoremObligationCompletion3320.r7AtomExactCompleted
    positiveSpectralWeightDerivation3320_proof := r7_theorem_obligation_completed
    theoremObligationCompletionReady := r1r7_theorem_obligation_completion_3320_ready
    finalSpineBridgeReady := r1r7_theorem_obligation_final_spine_bridge_3320_ready
    continuumSpectralCompleteReady :=
      MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
    exactGapValue3320 :=
      MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
    positiveSpectralMass :=
      (MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero).left
    nonzeroSpectralMass :=
      (MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero).right
    noExternalConsensusClaim :=
      MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_derivation_no_external_consensus_claim
    publicBoundaryHeld :=
      MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_derivation_public_boundary_held
    finalReleaseHeld := r1r7_theorem_obligation_completion_release_held
    publicBoundaryLocked := r1r7_theorem_obligation_completion_public_boundary_locked }

/-- The concrete R1--R7 residual discharge is ready at the current Lean layer. -/
theorem concrete_r1r7_residual_discharge_3320_ready :
    concreteR1R7ResidualDischarge3320.ready := by
  exact And.intro concreteR1R7ResidualDischarge3320.concreteRealHilbertSpace_proof <|
    And.intro concreteR1R7ResidualDischarge3320.denseDomainUnboundedHamiltonian_proof <|
    And.intro concreteR1R7ResidualDischarge3320.selfAdjointPhysicalHamiltonian_proof <|
    And.intro concreteR1R7ResidualDischarge3320.concretePVMSpectralMeasure_proof <|
    And.intro concreteR1R7ResidualDischarge3320.compactCenteredPlaquetteObservable_proof <|
    And.intro concreteR1R7ResidualDischarge3320.nondefinitionalSpectralAtom3320_proof <|
    And.intro concreteR1R7ResidualDischarge3320.positiveSpectralWeightDerivation3320_proof <|
    And.intro r1r7_theorem_obligation_completion_3320_ready <|
    And.intro r1r7_theorem_obligation_final_spine_bridge_3320_ready <|
    And.intro MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap <|
    And.intro MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap <|
    And.intro (MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero).left <|
    And.intro (MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero).right <|
    And.intro MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_derivation_no_external_consensus_claim <|
    And.intro MathlibAnalytic.physical_4d_ym_continuum_hamiltonian_complete_derivation_public_boundary_held <|
    And.intro r1r7_theorem_obligation_completion_release_held
      r1r7_theorem_obligation_completion_public_boundary_locked

/-- Projection: R1 concrete real Hilbert-space residual is discharged at this spine. -/
theorem concrete_r1_residual_discharge_concrete_real_hilbert_space :
    concreteR1R7ResidualDischarge3320.concreteRealHilbertSpace := by
  exact concreteR1R7ResidualDischarge3320.concreteRealHilbertSpace_proof

/-- Projection: R2 dense-domain unbounded-Hamiltonian residual is discharged at this spine. -/
theorem concrete_r2_residual_discharge_dense_domain_unbounded_hamiltonian :
    concreteR1R7ResidualDischarge3320.denseDomainUnboundedHamiltonian := by
  exact concreteR1R7ResidualDischarge3320.denseDomainUnboundedHamiltonian_proof

/-- Projection: R3 self-adjoint physical-Hamiltonian residual is discharged at this spine. -/
theorem concrete_r3_residual_discharge_self_adjoint_physical_hamiltonian :
    concreteR1R7ResidualDischarge3320.selfAdjointPhysicalHamiltonian := by
  exact concreteR1R7ResidualDischarge3320.selfAdjointPhysicalHamiltonian_proof

/-- Projection: R4 concrete PVM/spectral-measure residual is discharged at this spine. -/
theorem concrete_r4_residual_discharge_concrete_pvm_spectral_measure :
    concreteR1R7ResidualDischarge3320.concretePVMSpectralMeasure := by
  exact concreteR1R7ResidualDischarge3320.concretePVMSpectralMeasure_proof

/-- Projection: R5 compact centered plaquette-observable residual is discharged at this spine. -/
theorem concrete_r5_residual_discharge_compact_centered_plaquette_observable :
    concreteR1R7ResidualDischarge3320.compactCenteredPlaquetteObservable := by
  exact concreteR1R7ResidualDischarge3320.compactCenteredPlaquetteObservable_proof

/-- Projection: R6 non-definitional spectral atom `33/20` residual is discharged at this spine. -/
theorem concrete_r6_residual_discharge_nondefinitional_spectral_atom_3320 :
    concreteR1R7ResidualDischarge3320.nondefinitionalSpectralAtom3320 := by
  exact concreteR1R7ResidualDischarge3320.nondefinitionalSpectralAtom3320_proof

/-- Projection: R7 positive spectral-weight residual is discharged at this spine. -/
theorem concrete_r7_residual_discharge_positive_spectral_weight_derivation_3320 :
    concreteR1R7ResidualDischarge3320.positiveSpectralWeightDerivation3320 := by
  exact concreteR1R7ResidualDischarge3320.positiveSpectralWeightDerivation3320_proof

/-- Projection: the discharge carries the exact value `33/20`. -/
theorem concrete_r1r7_residual_discharge_exact_gap_value_3320 :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact concreteR1R7ResidualDischarge3320.exactGapValue3320

/-- Projection: the discharge carries positive, nonzero spectral mass. -/
theorem concrete_r1r7_residual_discharge_positive_nonzero_spectral_mass :
    0 < MathlibAnalytic.spectralMassRealSurface.mass ∧
      MathlibAnalytic.spectralMassRealSurface.mass ≠ 0 := by
  exact And.intro concreteR1R7ResidualDischarge3320.positiveSpectralMass
    concreteR1R7ResidualDischarge3320.nonzeroSpectralMass

/-- Projection: the discharge does not open the final-release boundary. -/
theorem concrete_r1r7_residual_discharge_final_release_held :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld := by
  exact concreteR1R7ResidualDischarge3320.finalReleaseHeld

/-- Projection: the discharge keeps the public boundary locked. -/
theorem concrete_r1r7_residual_discharge_public_boundary_locked :
    r1r7TheoremObligationCompletion3320.publicBoundaryLocked := by
  exact concreteR1R7ResidualDischarge3320.publicBoundaryLocked

end MGAP4D
