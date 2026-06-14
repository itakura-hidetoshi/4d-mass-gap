import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem os_wightman_reconstruction_spine_exact_hasHamiltonianMassGap
    (S : OSWightmanHamiltonianReconstructionSpine) :
    HasHamiltonianMassGap S.model.energySpectrum exactGapValueReal := by
  refine ⟨os_wightman_reconstruction_spine_exact_gap_positive S,
    S.model.vacuumEnergyZero, ?_⟩
  intro E hE hE0
  have hBddBelow :
      BddBelow (S.model.energySpectrum \ ({0} : Set ℝ)) := by
    refine ⟨0, ?_⟩
    intro x hx
    exact S.model.positiveEnergy x hx.1
  have hENonvacuum :
      E ∈ S.model.energySpectrum \ ({0} : Set ℝ) := by
    exact ⟨hE, by simpa using hE0⟩
  calc
    exactGapValueReal = S.model.massGapValue :=
      S.exact_gap_value_identified.symm
    _ = S.model.firstExcitation :=
      S.model.massGapValue_eq_firstExcitation
    _ = sInf (S.model.energySpectrum \ ({0} : Set ℝ)) :=
      S.model.firstExcitation_is_sInf_nonvacuum
    _ ≤ E := csInf_le hBddBelow hENonvacuum

theorem os_wightman_reconstruction_spine_exact_gap_mem_energySpectrum
    (S : OSWightmanHamiltonianReconstructionSpine) :
    exactGapValueReal ∈ S.model.energySpectrum := by
  rw [← S.exact_gap_value_identified,
    S.model.massGapValue_eq_firstExcitation]
  exact S.model.firstExcitation_mem

structure EuclideanYangMillsVacuumOrthogonalGapBridge where
  continuum : EuclideanYangMillsContinuumMeasureConstructionSpine
  explicitModel : ExplicitWightmanOSReconstructedModel
  explicitLegacyAxioms_identified :
    explicitModel.axioms.toLegacy = continuum.definitionBridge.spine.axioms
  hamiltonianSpectrum_identified :
    explicitModel.hamiltonianEnergySpectrum =
      continuum.definitionBridge.spine.model.energySpectrum
  pvmDisjointComposition :
    explicitModel.spectralPVM.HasDisjointCompositionZero
  nonzeroSpectralPVMWitness :
    ExplicitWightmanOSNonzeroSpectralPVMWitness explicitModel

theorem euclidean_yang_mills_vacuum_orthogonal_bridge_explicit_axioms_ready
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    B.explicitModel.axioms.toLegacy.ready := by
  rw [B.explicitLegacyAxioms_identified]
  exact euclidean_yang_mills_continuum_spine_os_axioms_ready B.continuum

theorem euclidean_yang_mills_vacuum_orthogonal_bridge_exact_hamiltonian_gap
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    HasHamiltonianMassGap
      B.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  rw [B.hamiltonianSpectrum_identified]
  exact os_wightman_reconstruction_spine_exact_hasHamiltonianMassGap
    B.continuum.definitionBridge.spine

theorem euclidean_yang_mills_vacuum_orthogonal_bridge_exact_gap_mem
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    exactGapValueReal ∈ B.explicitModel.hamiltonianEnergySpectrum := by
  rw [B.hamiltonianSpectrum_identified]
  exact os_wightman_reconstruction_spine_exact_gap_mem_energySpectrum
    B.continuum.definitionBridge.spine

def EuclideanYangMillsVacuumOrthogonalGapBridge.vacuumOrthogonalSpectrum
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge B.explicitModel :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    B.explicitModel B.pvmDisjointComposition B.nonzeroSpectralPVMWitness

theorem euclidean_yang_mills_vacuum_orthogonal_exact_gap
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    0 < exactGapValueReal ∧
      B.vacuumOrthogonalSpectrum.restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf B.vacuumOrthogonalSpectrum.restrictedSpectrum =
        exactGapValueReal := by
  have hGap :=
    euclidean_yang_mills_vacuum_orthogonal_bridge_exact_hamiltonian_gap B
  have hExactMem :=
    euclidean_yang_mills_vacuum_orthogonal_bridge_exact_gap_mem B
  exact ⟨hGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.vacuumOrthogonalSpectrum hGap,
    vacuum_orthogonal_restrictedSpectrum_sInf_eq
      B.vacuumOrthogonalSpectrum hGap hExactMem⟩

theorem euclidean_yang_mills_nonvacuum_hamiltonian_exact_gap
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    0 < exactGapValueReal ∧
      (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  have hPhysical := euclidean_yang_mills_vacuum_orthogonal_exact_gap B
  rw [B.vacuumOrthogonalSpectrum.restrictedSpectrum_eq_nonvacuum] at hPhysical
  exact hPhysical

end

end MathlibAnalytic
end MGAP4D
