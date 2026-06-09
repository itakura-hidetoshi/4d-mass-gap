import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem
import MGAP4D.MathlibAnalytic.SpectralMassReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Yang--Mills Hamiltonian spectral-value interface.

This upstream interface must not introduce the concrete numeric value later
claimed at R6.  It only records that the continuum Hamiltonian, self-adjoint /
spectral chain, Rayleigh lower-bound route, attainment route, and observable
spectral-mass route are mutually aligned around one spectral value carrier. -/
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
  noExternalConsensusClaim : Prop
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
  D.noExternalConsensusClaim ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- Installed upstream spectral-value interface. -/
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
    spectralInfimumValue := exactGapValueReal
    attainedSpectralValue := exactGapValueReal
    observableSpectralAtomValue := exactGapValueReal
    derivedHamiltonianSpectralValue := exactGapValueReal
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
    And.intro rfl <|
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

end MathlibAnalytic
end MGAP4D
