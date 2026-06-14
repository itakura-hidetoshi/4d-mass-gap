import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import MGAP4D.MathlibAnalytic.WightmanOSConnectedCorrelationSpectralGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Euclidean-to-physical mass-gap bridge driven by connected-correlation
Laplace bounds rather than by the legacy `firstExcitation_pos` field.

The continuum construction spine identifies the OS/Wightman axiom package.  The
explicit reconstructed model supplies the Hilbert space, Hamiltonian, vacuum,
and PVM.  The correlation package supplies the actual analytic input
`w(E) exp(-E t) ≤ C(t) ≤ C exp(-Δ t)`. -/
structure EuclideanYangMillsConnectedCorrelationGapBridge where
  continuum : EuclideanYangMillsContinuumMeasureConstructionSpine
  explicitModel : ExplicitWightmanOSReconstructedModel
  explicitLegacyAxioms_identified :
    explicitModel.axioms.toLegacy = continuum.definitionBridge.spine.axioms
  pvmDisjointComposition :
    explicitModel.spectralPVM.HasDisjointCompositionZero
  nonzeroSpectralPVMWitness :
    ExplicitWightmanOSNonzeroSpectralPVMWitness explicitModel
  vacuumEnergySpectralValue :
    0 ∈ explicitModel.hamiltonianEnergySpectrum
  correlationLaplaceBounds :
    ExplicitWightmanOSConnectedCorrelationLaplaceBounds
      explicitModel exactGapValueReal

/-- The Euclidean continuum spine still supplies the OS/Wightman readiness
statement on the explicitly reconstructed model. -/
theorem euclidean_connected_correlation_bridge_explicit_axioms_ready
    (B : EuclideanYangMillsConnectedCorrelationGapBridge) :
    B.explicitModel.axioms.toLegacy.ready := by
  rw [B.explicitLegacyAxioms_identified]
  exact euclidean_yang_mills_continuum_spine_os_axioms_ready B.continuum

/-- Main independent Hamiltonian-gap theorem.  No use is made of
`firstExcitation`, `firstExcitation_pos`, or
`massGapValue_eq_firstExcitation`. -/
theorem euclidean_connected_correlation_exact_hasHamiltonianMassGap
    (B : EuclideanYangMillsConnectedCorrelationGapBridge) :
    HasHamiltonianMassGap
      B.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact connected_correlation_laplace_bounds_hasHamiltonianMassGap
    B.correlationLaplaceBounds B.vacuumEnergySpectralValue

/-- Canonical physical non-vacuum spectrum bridge obtained from the PVM law and
one nonzero spectral vector. -/
def EuclideanYangMillsConnectedCorrelationGapBridge.vacuumOrthogonalSpectrum
    (B : EuclideanYangMillsConnectedCorrelationGapBridge) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge B.explicitModel :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    B.explicitModel B.pvmDisjointComposition B.nonzeroSpectralPVMWitness

/-- Connected-correlation decay gives a strictly positive lower spectral edge on
`Ω⊥`, without assuming that the edge is attained. -/
theorem euclidean_connected_correlation_vacuum_orthogonal_lower_bound
    (B : EuclideanYangMillsConnectedCorrelationGapBridge) :
    0 < exactGapValueReal ∧
      B.vacuumOrthogonalSpectrum.restrictedSpectrum ⊆
        Set.Ici exactGapValueReal := by
  have hGap :=
    euclidean_connected_correlation_exact_hasHamiltonianMassGap B
  exact ⟨hGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.vacuumOrthogonalSpectrum hGap⟩

/-- If the exact decay threshold is also a Hamiltonian spectral point, it is the
infimum of the physical non-vacuum spectrum. -/
theorem euclidean_connected_correlation_vacuum_orthogonal_exact_gap
    (B : EuclideanYangMillsConnectedCorrelationGapBridge)
    (hExactSpectrum :
      exactGapValueReal ∈ B.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      B.vacuumOrthogonalSpectrum.restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf B.vacuumOrthogonalSpectrum.restrictedSpectrum =
        exactGapValueReal := by
  have hGap :=
    euclidean_connected_correlation_exact_hasHamiltonianMassGap B
  exact ⟨hGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.vacuumOrthogonalSpectrum hGap,
    vacuum_orthogonal_restrictedSpectrum_sInf_eq
      B.vacuumOrthogonalSpectrum hGap hExactSpectrum⟩

/-- Familiar spectrum-minus-vacuum form of the exact theorem. -/
theorem euclidean_connected_correlation_nonvacuum_exact_gap
    (B : EuclideanYangMillsConnectedCorrelationGapBridge)
    (hExactSpectrum :
      exactGapValueReal ∈ B.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  have hPhysical :=
    euclidean_connected_correlation_vacuum_orthogonal_exact_gap
      B hExactSpectrum
  rw [B.vacuumOrthogonalSpectrum.restrictedSpectrum_eq_nonvacuum] at hPhysical
  exact hPhysical

end

end MathlibAnalytic
end MGAP4D
