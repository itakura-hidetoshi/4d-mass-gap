import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitness

namespace MGAP4D
namespace MathlibAnalytic

/-- Theorem-derived hardening bundle for the continuum-Hamiltonian mass-gap
witness surface.

This additive surface does not replace the existing witness object. It exposes
its principal review slots through upstream theorem-derived witnesses from the
continuum Yang--Mills hardening lane and the plaquette spectral-weight hardening
lane.

Boundary and alignment: the exact-value component of this bundle keeps the
positive `exactGapValueReal` carrier together with the exact-value derivation
boundary, rather than re-exporting the numerical equality upstream.  The
installed route derives the normalized value through
`YangMillsHamiltonianSpectralDerivation3320` and the complete
continuum-Hamiltonian derivation, while this bundle keeps the carrier/witness
slots available for that downstream derivation route. -/
theorem continuum_hamiltonian_mass_gap_witness_hardened_bundle :
    continuumYangMillsLaneHardeningData.concreteYMHardened ∧
      continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened ∧
      (selfAdjointHPhysLaneHardeningData.ready ∧
        spectralRealizationSkeletonReviewSurface.ready ∧
        continuumSpectralTheoremSkeletonReviewSurface.ready) ∧
      (PhysicalHamiltonianNormalizationBridgeReviewSurface.ready
          physicalHamiltonianNormalizationBridgeReviewSurface ∧
        exactGapValueDerivationBoundary.ready) ∧
      (plaquetteSpectralWeightLaneHardeningData.compactSupportHardened ∧
        plaquetteSpectralWeightLaneHardeningData.centeredHardened ∧
        plaquetteSpectralWeightLaneHardeningData.smearedHardened) ∧
      (plaquetteSpectralWeightLaneHardeningData.observableAtomHardened ∧
        plaquetteSpectralWeightLaneHardeningData.positiveWeightHardened ∧
        plaquetteSpectralWeightLaneHardeningData.nonzeroWeightHardened) ∧
      (0 < exactGapValueReal ∧ exactGapValueDerivationBoundary.ready) ∧
      (continuumYangMillsLaneHardeningData.ready ∧
        plaquetteSpectralWeightLaneHardeningData.ready) ∧
      continuumHamiltonianMassGapWitnessData.ready := by
  exact And.intro
    (continuum_ym_concrete_skeleton_hardened
      continuumYangMillsLaneHardeningData
      continuum_yang_mills_lane_hardening_ready) <|
    And.intro
      (continuum_ym_hphys_built_from_ym_hardened
        continuumYangMillsLaneHardeningData
        continuum_yang_mills_lane_hardening_ready) <|
    And.intro
      (And.intro continuumYangMillsLaneHardeningData.selfAdjointLaneReady <|
        And.intro continuumYangMillsLaneHardeningData.spectralSkeletonReady
          continuumYangMillsLaneHardeningData.continuumSpectralReady) <|
    And.intro
      (And.intro continuumYangMillsLaneHardeningData.normalizationBridgeReady
        exact_gap_value_derivation_boundary_ready) <|
    And.intro
      (And.intro
        (plaquette_weight_compact_support_hardened
          plaquetteSpectralWeightLaneHardeningData
          plaquette_spectral_weight_lane_hardening_ready) <|
        And.intro
          (plaquette_weight_centered_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)
          (plaquette_weight_smeared_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)) <|
    And.intro
      (And.intro
        (plaquette_weight_observable_atom_hardened
          plaquetteSpectralWeightLaneHardeningData
          plaquette_spectral_weight_lane_hardening_ready) <|
        And.intro
          (plaquette_weight_positive_weight_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)
          (plaquette_weight_nonzero_weight_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)) <|
    And.intro
      (And.intro exactGapValueReal_pos exact_gap_value_derivation_boundary_ready) <|
    And.intro
      (And.intro continuum_yang_mills_lane_hardening_ready
        plaquette_spectral_weight_lane_hardening_ready)
      continuum_hamiltonian_mass_gap_witness_ready

/-- The hardened bundle exposes the physical continuum-Hamiltonian witness. -/
theorem continuum_hamiltonian_physical_witness_from_hardened_bundle :
    continuumYangMillsLaneHardeningData.concreteYMHardened := by
  exact continuum_hamiltonian_mass_gap_witness_hardened_bundle.1

/-- The hardened bundle exposes the `H_phys`-from-Yang--Mills witness. -/
theorem continuum_hamiltonian_hphys_from_ym_witness_from_hardened_bundle :
    continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened := by
  exact continuum_hamiltonian_mass_gap_witness_hardened_bundle.2.1

/-- The hardened bundle exposes positivity of the carrier together with the
exact-value derivation boundary.  The spectral derivation using this carrier is
recorded by the dedicated Yang--Mills Hamiltonian spectral derivation route. -/
theorem continuum_hamiltonian_exact_positive_mass_gap_from_hardened_bundle :
    0 < exactGapValueReal ∧ exactGapValueDerivationBoundary.ready := by
  exact continuum_hamiltonian_mass_gap_witness_hardened_bundle.2.2.2.2.2.2.1

/-- The hardened bundle still points back to the installed witness surface. -/
theorem continuum_hamiltonian_installed_witness_ready_from_hardened_bundle :
    continuumHamiltonianMassGapWitnessData.ready := by
  exact continuum_hamiltonian_mass_gap_witness_hardened_bundle.2.2.2.2.2.2.2.2

/-- Boundary projection: the hardened bundle preserves the exact-value derivation
boundary and feeds the downstream spectral derivation route, rather than claiming
that the carrier equality alone is the Yang--Mills spectral theorem. -/
theorem continuum_hamiltonian_hardened_bundle_exact_gap_value_derivation_boundary :
    exactGapValueDerivationBoundary.ready := by
  exact exact_gap_value_derivation_boundary_ready

end MathlibAnalytic
end MGAP4D
