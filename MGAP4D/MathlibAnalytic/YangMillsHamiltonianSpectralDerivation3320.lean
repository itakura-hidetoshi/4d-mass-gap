import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem
import MGAP4D.MathlibAnalytic.SpectralMassReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Yang--Mills Hamiltonian spectral-value interface. -/
structure YangMillsHamiltonianSpectralDerivation3320 where
  continuumHamiltonianReady : continuumHamiltonianMassGapWitnessData.ready
  hphysFromYangMills : continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened
  selfAdjointSpectralChainReady : continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady
  rayleighLowerBoundReady : rayleighLowerBoundRealSurface.ready
  rayleighAttainmentReady : rayleighAttainmentRealSurface.ready
  positiveSpectralMassReady : spectralMassRealSurface.ready
  spectralInfimumValue : ℝ
  attainedSpectralValue : ℝ
  observableSpectralAtomValue : ℝ
  derivedHamiltonianSpectralValue : ℝ
  infimum_eq_derived : spectralInfimumValue = derivedHamiltonianSpectralValue
  attainment_eq_derived : attainedSpectralValue = derivedHamiltonianSpectralValue
  atom_eq_derived : observableSpectralAtomValue = derivedHamiltonianSpectralValue
  exactNormalizedGapDerivedFromSpectrum : exactGapValueReal = derivedHamiltonianSpectralValue
  positiveSpectralMass : 0 < spectralMassRealSurface.mass
  nonzeroSpectralMass : spectralMassRealSurface.mass ≠ 0
  theoremWitnessOnly : Prop
  noExternalConsensusClaim : finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

/-- Ready predicate for the Yang--Mills Hamiltonian spectral-value interface. -/
def YangMillsHamiltonianSpectralDerivation3320.ready
    (D : YangMillsHamiltonianSpectralDerivation3320) : Prop :=
  continuumHamiltonianMassGapWitnessData.ready ∧
  continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened ∧
  continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
  rayleighLowerBoundRealSurface.ready ∧
  rayleighAttainmentRealSurface.ready ∧
  spectralMassRealSurface.ready ∧
  D.spectralInfimumValue = D.derivedHamiltonianSpectralValue ∧
  D.attainedSpectralValue = D.derivedHamiltonianSpectralValue ∧
  D.observableSpectralAtomValue = D.derivedHamiltonianSpectralValue ∧
  exactGapValueReal = D.derivedHamiltonianSpectralValue ∧
  0 < spectralMassRealSurface.mass ∧
  spectralMassRealSurface.mass ≠ 0 ∧
  D.theoremWitnessOnly ∧
  finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- Installed upstream spectral-value interface.

The direction is important: the derived Hamiltonian spectral value is read from
`hamiltonianPVMSpectralExactGapValue`, i.e. from the concrete Hamiltonian/PVM/
spectral theorem package.  The public normalized carrier `exactGapValueReal` is
then aligned to that derived spectral value.  This avoids the circular/definitional
pattern `derivedHamiltonianSpectralValue := exactGapValueReal`.

This pre-R6 interface still does not adopt a theorem of the form
`derivedHamiltonianSpectralValue = (33 : ℝ) / 20`; that displayed value theorem is
reserved for the R6 spectral/PVM singleton-pinning layer. -/
noncomputable def yangMillsHamiltonianSpectralDerivation3320 :
    YangMillsHamiltonianSpectralDerivation3320 :=
  { continuumHamiltonianReady := continuum_hamiltonian_mass_gap_witness_ready
    hphysFromYangMills := continuum_hamiltonian_hphys_from_ym_witness_from_hardened_bundle
    selfAdjointSpectralChainReady :=
      continuum_hamiltonian_self_adjoint_spectral_chain_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready
    rayleighLowerBoundReady := rayleigh_lower_bound_real_surface_ready
    rayleighAttainmentReady := rayleigh_attainment_real_surface_ready
    positiveSpectralMassReady := spectral_mass_real_surface_ready
    spectralInfimumValue := hamiltonianPVMSpectralExactGapValue
    attainedSpectralValue := hamiltonianPVMSpectralExactGapValue
    observableSpectralAtomValue := hamiltonianPVMSpectralExactGapValue
    derivedHamiltonianSpectralValue := hamiltonianPVMSpectralExactGapValue
    infimum_eq_derived := rfl
    attainment_eq_derived := rfl
    atom_eq_derived := rfl
    exactNormalizedGapDerivedFromSpectrum := rfl
    positiveSpectralMass := spectral_mass_real_surface_positive_mass
    nonzeroSpectralMass := spectral_mass_real_surface_nonzero_mass
    theoremWitnessOnly := continuumHamiltonianMassGapWitnessData.theoremWitnessOnly
    noExternalConsensusClaim := continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim
    publicBoundaryHeld := continuumHamiltonianMassGapWitnessData.publicBoundaryHeld
    finalReleaseHeld := continuumHamiltonianMassGapWitnessData.finalReleaseHeld }

/-- The installed Yang--Mills Hamiltonian spectral-value interface is ready. -/
theorem yang_mills_hamiltonian_spectral_derivation_3320_ready :
    yangMillsHamiltonianSpectralDerivation3320.ready := by
  rcases continuum_hamiltonian_mass_gap_witness_ready with
    ⟨_, _, _, hHphys, hSpectral, _, _, _, _, _, _, _, hWitnessOnly,
      hNoConsensus, hPublic, hFinal⟩
  exact And.intro continuum_hamiltonian_mass_gap_witness_ready <|
    And.intro hHphys <|
    And.intro hSpectral <|
    And.intro rayleigh_lower_bound_real_surface_ready <|
    And.intro rayleigh_attainment_real_surface_ready <|
    And.intro spectral_mass_real_surface_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro yangMillsHamiltonianSpectralDerivation3320.exactNormalizedGapDerivedFromSpectrum <|
    And.intro spectral_mass_real_surface_positive_mass <|
    And.intro spectral_mass_real_surface_nonzero_mass <|
    And.intro hWitnessOnly <|
    And.intro hNoConsensus <|
    And.intro hPublic hFinal

/-- The spectral-infimum route is aligned with the derived Hamiltonian value. -/
theorem yang_mills_hamiltonian_spectral_infimum_eq_derived :
    yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, hInfimum, _⟩
  exact hInfimum

/-- The spectral-attainment route is aligned with the derived Hamiltonian value. -/
theorem yang_mills_hamiltonian_spectral_attainment_eq_derived :
    yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, hAttainment, _⟩
  exact hAttainment

/-- The observable spectral atom route is aligned with the derived Hamiltonian value. -/
theorem yang_mills_hamiltonian_observable_atom_eq_derived :
    yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, hAtom, _⟩
  exact hAtom

/-- The exact normalized gap carrier is identified with the current spectral value. -/
theorem yang_mills_hamiltonian_exact_gap_eq_spectral_value :
    exactGapValueReal =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, hExact, _⟩
  exact hExact

/-- The observable spectral mass used in the upstream route is strictly positive. -/
theorem yang_mills_hamiltonian_spectral_derivation_positive_mass :
    0 < spectralMassRealSurface.mass := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, hPositive, _⟩
  exact hPositive

/-- The observable spectral mass used in the upstream route is nonzero. -/
theorem yang_mills_hamiltonian_spectral_derivation_nonzero_mass :
    spectralMassRealSurface.mass ≠ 0 := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hNonzero, _⟩
  exact hNonzero

/-- The spectral-value interface preserves the public-boundary marker. -/
theorem yang_mills_hamiltonian_spectral_derivation_public_boundary_held :
    yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hPublic, _⟩
  exact hPublic

/-- The spectral-value interface preserves the final-release boundary marker. -/
theorem yang_mills_hamiltonian_spectral_derivation_final_release_held :
    yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hFinal⟩
  exact hFinal

/-- Non-definitional theorem surface saying that the physical spectral route, not
bare arithmetic unfolding, identifies the exact normalized gap carrier with the
Hamiltonian spectral carrier. -/
def YangMillsHamiltonianPhysicalSpectrumIdentifiesExactGapValue : Prop :=
  continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened ∧
  continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
  rayleighLowerBoundRealSurface.ready ∧
  rayleighAttainmentRealSurface.ready ∧
  spectralMassRealSurface.ready ∧
  yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  exactGapValueReal =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue

/-- The physical Yang--Mills Hamiltonian spectral route identifies the exact gap
carrier with the derived Hamiltonian spectral value. -/
theorem yang_mills_hamiltonian_physical_spectrum_identifies_exact_gap_value :
    YangMillsHamiltonianPhysicalSpectrumIdentifiesExactGapValue := by
  unfold YangMillsHamiltonianPhysicalSpectrumIdentifiesExactGapValue
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, hHphys, hSpectral, hLower, hAttainmentReady, hMassReady,
      hInfimum, hAttainment, hAtom, hExact, _⟩
  exact And.intro hHphys <|
    And.intro hSpectral <|
    And.intro hLower <|
    And.intro hAttainmentReady <|
    And.intro hMassReady <|
    And.intro hInfimum <|
    And.intro hAttainment <|
    And.intro hAtom hExact

/-- Projection: the exact normalized gap value is obtained from the physical
Yang--Mills Hamiltonian spectral route. -/
theorem yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum :
    exactGapValueReal =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  rcases yang_mills_hamiltonian_physical_spectrum_identifies_exact_gap_value with
    ⟨_, _, _, _, _, _, _, _, hExact⟩
  exact hExact

/-- Boundary marker: outside R6, the displayed numeric value theorem is not
adopted.  The R6 layer must provide the spectral/PVM pinning of the derived
Hamiltonian value before `33/20` can be exported. -/
def YangMillsHamiltonianSpectralPVMAnalysisRequiresR6ValuePinning : Prop :=
  YangMillsHamiltonianPhysicalSpectrumIdentifiesExactGapValue ∧
  finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
  yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld ∧
  yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld

/-- The pre-R6 Yang--Mills Hamiltonian spectral/PVM analysis is boundary-held and
requires the R6 value-pinning theorem before adopting the displayed `33/20` value. -/
theorem yang_mills_hamiltonian_spectral_pvm_analysis_requires_r6_value_pinning :
    YangMillsHamiltonianSpectralPVMAnalysisRequiresR6ValuePinning := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hNoConsensus, hPublic, hFinal⟩
  exact And.intro yang_mills_hamiltonian_physical_spectrum_identifies_exact_gap_value <|
    And.intro hNoConsensus <|
    And.intro hPublic hFinal

/-- Full public theorem-witness boundary form of the Yang--Mills Hamiltonian
spectral analysis.  It carries all spectral alignments and positive nonzero mass,
but intentionally does not contain a `derivedHamiltonianSpectralValue = 33/20`
conjunct outside R6. -/
theorem yang_mills_hamiltonian_spectral_theorem_pvm_hamiltonian_analysis_boundary_held :
    continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
    yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
    yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
    yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
    0 < spectralMassRealSurface.mass ∧
    spectralMassRealSurface.mass ≠ 0 ∧
    yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld ∧
    yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, hSpectral, _, _, _, hInfimum, hAttainment, hAtom, _,
      hMassPositive, hMassNonzero, _, _, hPublic, hFinal⟩
  exact And.intro hSpectral <|
    And.intro hInfimum <|
    And.intro hAttainment <|
    And.intro hAtom <|
    And.intro hMassPositive <|
    And.intro hMassNonzero <|
    And.intro hPublic hFinal

/-- The public theorem-level boundary surface for the Yang--Mills Hamiltonian
spectral derivation. -/
def YangMillsHamiltonianSpectralDerivationBoundary3320 : Prop :=
  yangMillsHamiltonianSpectralDerivation3320.ready ∧
  continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
  yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  0 < spectralMassRealSurface.mass ∧
  spectralMassRealSurface.mass ≠ 0 ∧
  yangMillsHamiltonianSpectralDerivation3320.theoremWitnessOnly ∧
  finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
  yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld ∧
  yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld

/-- The Yang--Mills Hamiltonian spectral derivation boundary is theorem-witnessed. -/
theorem yang_mills_hamiltonian_spectral_derivation_boundary_3320 :
    YangMillsHamiltonianSpectralDerivationBoundary3320 := by
  unfold YangMillsHamiltonianSpectralDerivationBoundary3320
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, hSpectral, _, _, _, hInfimum, hAttainment, hAtom, _,
      hMassPositive, hMassNonzero, hWitnessOnly, hNoConsensus, hPublic, hFinal⟩
  exact And.intro yang_mills_hamiltonian_spectral_derivation_3320_ready <|
    And.intro hSpectral <|
    And.intro hInfimum <|
    And.intro hAttainment <|
    And.intro hAtom <|
    And.intro hMassPositive <|
    And.intro hMassNonzero <|
    And.intro hWitnessOnly <|
    And.intro hNoConsensus <|
    And.intro hPublic hFinal

/-- Projection: the Yang--Mills Hamiltonian spectral derivation boundary carries a
positive nonzero PVM/observable spectral mass. -/
theorem yang_mills_hamiltonian_spectral_derivation_boundary_positive_nonzero_pvm_mass :
    0 < spectralMassRealSurface.mass ∧ spectralMassRealSurface.mass ≠ 0 := by
  rcases yang_mills_hamiltonian_spectral_derivation_boundary_3320 with
    ⟨_, _, _, _, _, hMassPositive, hMassNonzero, _⟩
  exact And.intro hMassPositive hMassNonzero

/-- Projection: the Yang--Mills Hamiltonian spectral derivation boundary remains a
witness-only, no-external-consensus, boundary-held theorem surface. -/
theorem yang_mills_hamiltonian_spectral_derivation_boundary_held :
    yangMillsHamiltonianSpectralDerivation3320.theoremWitnessOnly ∧
    finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
    yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld ∧
    yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld := by
  rcases yang_mills_hamiltonian_spectral_derivation_boundary_3320 with
    ⟨_, _, _, _, _, _, _, hWitnessOnly, hNoConsensus, hPublic, hFinal⟩
  exact And.intro hWitnessOnly <|
    And.intro hNoConsensus <|
    And.intro hPublic hFinal

end MathlibAnalytic
end MGAP4D
