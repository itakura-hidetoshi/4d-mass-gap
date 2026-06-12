import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine

namespace MGAP4D
namespace MathlibAnalytic

/-- Reconstruct the induced-pipeline full spectral package from the construction
certificate fields themselves.

Unlike the wrapper theorem in the construction-spine module, this bridge consumes
`C.massGapTheorem`, `C.deltaPositive`, `C.nonVacuumThreshold`,
`C.nonVacuumEnergyLowerBound`, and `C.firstExcitationPVMDetected` explicitly. -/
theorem euclidean_yang_mills_continuum_spine_certificate_only_induced_pipeline_full_spectral_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ, E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum → δ ≤ E) ∧
    ∃ ψ : S.toPipeline.definitionBridge.spine.model.H,
      ψ ∈ S.toPipeline.definitionBridge.spine.model.spectralPVM
        ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  rcases C.nonVacuumEnergyLowerBound with ⟨δ, hδPositive, hLower⟩
  exact ⟨
    C.massGapTheorem,
    C.deltaPositive,
    C.nonVacuumThreshold,
    ⟨δ, hδPositive,
      fun E hE => hLower E (by
        simpa [euclidean_yang_mills_continuum_spine_toPipeline_nonvacuum_spectrum S]
          using hE)⟩,
    by
      simpa [euclidean_yang_mills_continuum_spine_toPipeline_definitionBridge S]
        using C.firstExcitationPVMDetected⟩

end MathlibAnalytic
end MGAP4D
