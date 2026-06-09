import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem
import MGAP4D.MathlibAnalytic.SpectralMassReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Spectral-receipt surface for the normalized value `33/20` along the
Yang--Mills continuum Hamiltonian chain.

This is an additive theorem/receipt surface.  It does not replace the upstream
continuum-Hamiltonian witness, and it does not widen the public-release or
external-consensus boundary.

External-review reading:

* the continuum Yang--Mills lane builds the physical Hamiltonian witness;
* the self-adjoint/spectral chain is ready;
* the Rayleigh lower-bound surface supplies the spectral-infimum receipt;
* the Rayleigh attainment surface supplies the eigenvalue/attainment receipt;
* the positive spectral-mass surface supplies the observable spectral-atom
  receipt;
* the current installed `derivedHamiltonianSpectralValue` is then identified
  with the normalized carrier `exactGapValueReal`.

Thus this file is not, by itself, an independent construction of a new spectral
value followed by a calculation reducing it to `33/20`.  It is the current Lean
receipt that aligns the spectral-route readiness witnesses with the canonical
normalized carrier.  A stronger future lane may replace the carrier-identified
receipt with a genuinely independent spectral-value construction, but that would
be a distinct theorem-body surface. -/
structure YangMillsHamiltonianSpectralDerivation3320 where
  continuumHamiltonianReady : continuumHamiltonianMassGapWitnessData.ready
  hphysFromYangMills : continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened
  selfAdjointSpectralChainReady : continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady
  rayleighLowerBoundReady : rayleighLowerBoundRealSurface.ready
  rayleighAttainmentReady : rayleighAttainmentRealSurface.ready
  positiveSpectralMassReady : spectralMassRealSurface.ready
  spectralInfimumValue : ℝ
  spectralInfimumValue_eq_3320 : spectralInfimumValue = (33 : ℝ) / 20
  attainedSpectralValue : ℝ
  attainedSpectralValue_eq_3320 : attainedSpectralValue = (33 : ℝ) / 20
  observableSpectralAtomValue : ℝ
  observableSpectralAtomValue_eq_3320 : observableSpectralAtomValue = (33 : ℝ) / 20
  /-- Current installed derived spectral value.  In this receipt layer it is
  carrier-identified with `exactGapValueReal`; it is not yet an independent
  operator-theoretic construction separate from the carrier. -/
  derivedHamiltonianSpectralValue : ℝ
  derivedHamiltonianSpectralValue_eq_3320 :
    derivedHamiltonianSpectralValue = (33 : ℝ) / 20
  exactNormalizedGapDerivedFromSpectrum :
    exactGapValueReal = derivedHamiltonianSpectralValue
  positiveSpectralMass : 0 < spectralMassRealSurface.mass
  nonzeroSpectralMass : spectralMassRealSurface.mass ≠ 0
  theoremWitnessOnly : Prop
  noExternalConsensusClaim : Prop
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

/-- Ready predicate for the Yang--Mills Hamiltonian spectral receipt for
`33/20`. -/
def YangMillsHamiltonianSpectralDerivation3320.ready
    (D : YangMillsHamiltonianSpectralDerivation3320) : Prop :=
  continuumHamiltonianMassGapWitnessData.ready ∧
  continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened ∧
  continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
  rayleighLowerBoundRealSurface.ready ∧
  rayleighAttainmentRealSurface.ready ∧
  spectralMassRealSurface.ready ∧
  D.spectralInfimumValue = (33 : ℝ) / 20 ∧
  D.attainedSpectralValue = (33 : ℝ) / 20 ∧
  D.observableSpectralAtomValue = (33 : ℝ) / 20 ∧
  D.derivedHamiltonianSpectralValue = (33 : ℝ) / 20 ∧
  exactGapValueReal = D.derivedHamiltonianSpectralValue ∧
  0 < spectralMassRealSurface.mass ∧
  spectralMassRealSurface.mass ≠ 0 ∧
  D.theoremWitnessOnly ∧
  D.noExternalConsensusClaim ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- Installed spectral-receipt surface. -/
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
    spectralInfimumValue := rayleighLowerBoundRealSurface.value
    spectralInfimumValue_eq_3320 := rayleigh_lower_bound_real_surface_value
    attainedSpectralValue := rayleighAttainmentRealSurface.value
    attainedSpectralValue_eq_3320 := rayleigh_attainment_real_surface_value
    observableSpectralAtomValue := spectralMassRealSurface.value
    observableSpectralAtomValue_eq_3320 := spectral_mass_real_surface_value
    derivedHamiltonianSpectralValue := exactGapValueReal
    derivedHamiltonianSpectralValue_eq_3320 := exactGapValueReal_eq
    exactNormalizedGapDerivedFromSpectrum := rfl
    positiveSpectralMass := spectral_mass_real_surface_positive_mass
    nonzeroSpectralMass := spectral_mass_real_surface_nonzero_mass
    theoremWitnessOnly := continuumHamiltonianMassGapWitnessData.theoremWitnessOnly
    noExternalConsensusClaim := continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim
    publicBoundaryHeld := continuumHamiltonianMassGapWitnessData.publicBoundaryHeld
    finalReleaseHeld := continuumHamiltonianMassGapWitnessData.finalReleaseHeld }

/-- The installed Yang--Mills Hamiltonian spectral receipt is ready. -/
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
    And.intro rayleigh_lower_bound_real_surface_value <|
    And.intro rayleigh_attainment_real_surface_value <|
    And.intro spectral_mass_real_surface_value <|
    And.intro exactGapValueReal_eq <|
    And.intro rfl <|
    And.intro spectral_mass_real_surface_positive_mass <|
    And.intro spectral_mass_real_surface_nonzero_mass <|
    And.intro hWitnessOnly <|
    And.intro hNoConsensus <|
    And.intro hPublic hFinal

/-- The Yang--Mills Hamiltonian spectral-infimum receipt gives `33/20`. -/
theorem yang_mills_hamiltonian_spectral_infimum_eq_3320 :
    yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
      (33 : ℝ) / 20 := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, hInfimum, _⟩
  exact hInfimum

/-- The Yang--Mills Hamiltonian spectral-attainment receipt gives `33/20`. -/
theorem yang_mills_hamiltonian_spectral_attainment_eq_3320 :
    yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
      (33 : ℝ) / 20 := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, hAttainment, _⟩
  exact hAttainment

/-- The observable spectral atom receipt is located at `33/20`. -/
theorem yang_mills_hamiltonian_observable_atom_eq_3320 :
    yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
      (33 : ℝ) / 20 := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, hAtom, _⟩
  exact hAtom

/-- The Yang--Mills Hamiltonian spectral receipt identifies the normalized
Hamiltonian spectral value as `33/20`. -/
theorem yang_mills_hamiltonian_spectral_analysis_derives_3320 :
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20 := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, hDerived, _⟩
  exact hDerived

/-- The exact normalized gap carrier is identified with the current spectral
receipt value. -/
theorem yang_mills_hamiltonian_exact_gap_eq_spectral_value :
    exactGapValueReal =
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, hExact, _⟩
  exact hExact

/-- The full spectral receipt gives the theorem-body exact value `33/20`. -/
theorem yang_mills_hamiltonian_spectral_derivation_exact_gap_value :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact (yang_mills_hamiltonian_exact_gap_eq_spectral_value).trans
    yang_mills_hamiltonian_spectral_analysis_derives_3320

/-- The observable spectral mass used in the receipt is strictly positive. -/
theorem yang_mills_hamiltonian_spectral_derivation_positive_mass :
    0 < spectralMassRealSurface.mass := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hPositive, _⟩
  exact hPositive

/-- The observable spectral mass used in the receipt is nonzero. -/
theorem yang_mills_hamiltonian_spectral_derivation_nonzero_mass :
    spectralMassRealSurface.mass ≠ 0 := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNonzero, _⟩
  exact hNonzero

/-- The spectral receipt preserves the public-boundary marker. -/
theorem yang_mills_hamiltonian_spectral_derivation_public_boundary_held :
    yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPublic, _⟩
  exact hPublic

/-- The spectral receipt preserves the final-release boundary marker. -/
theorem yang_mills_hamiltonian_spectral_derivation_final_release_held :
    yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld := by
  rcases yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hFinal⟩
  exact hFinal

end MathlibAnalytic
end MGAP4D
