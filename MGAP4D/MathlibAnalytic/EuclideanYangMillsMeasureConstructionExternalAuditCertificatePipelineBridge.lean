import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge

namespace MGAP4D
namespace MathlibAnalytic

/-- Reconstruct the induced-pipeline full spectral package directly from the
external-audit construction-spine certificate fields.

This theorem makes the certificate-only dependency path explicit rather than
routing through the construction spine's direct package theorem. -/
theorem external_audit_readiness_euclidean_construction_spine_certificate_only_induced_pipeline_full_spectral_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
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
    by
      simpa [euclidean_yang_mills_continuum_spine_toPipeline_definitionBridge S]
        using C.massGapDefinition,
    C.exactGapPositive,
    by
      simpa [euclidean_yang_mills_continuum_spine_toPipeline_nonvacuum_spectrum S]
        using C.exactGapThreshold,
    ⟨δ, hδPositive,
      fun E hE => hLower E (by
        simpa [euclidean_yang_mills_continuum_spine_toPipeline_nonvacuum_spectrum S]
          using hE)⟩,
    by
      simpa [euclidean_yang_mills_continuum_spine_toPipeline_definitionBridge S]
        using C.firstExcitationPVMDetected⟩

end MathlibAnalytic
end MGAP4D
