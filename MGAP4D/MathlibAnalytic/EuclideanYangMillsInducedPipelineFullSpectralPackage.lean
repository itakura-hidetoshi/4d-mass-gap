import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionCertificatePipelineBridge
import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditCertificatePipelineBridge

namespace MGAP4D
namespace MathlibAnalytic

/-- Named carrier for the full spectral package on the induced Euclidean
measure-to-mass-gap pipeline.

The structure avoids repeatedly exposing the same deeply nested conjunction to
downstream files while preserving each audit-visible spectral component. -/
structure EuclideanYangMillsInducedPipelineFullSpectralPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  massGap : S.toPipeline.definitionBridge.spine.model.hasMassGap
  exactGapPositive : 0 < exactGapValueReal
  exactGapThreshold :
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum
  nonVacuumEnergyLowerBound :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ, E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum → δ ≤ E
  firstExcitationPVMDetected :
    ∃ ψ : S.toPipeline.definitionBridge.spine.model.H,
      ψ ∈ S.toPipeline.definitionBridge.spine.model.spectralPVM
        ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ)

/-- Build the named package directly from the construction spine. -/
def euclideanYangMillsInducedPipelineFullSpectralPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsInducedPipelineFullSpectralPackage S := by
  rcases euclidean_yang_mills_continuum_spine_toPipeline_full_spectral_package S with
    ⟨hMassGap, hPositive, hThreshold, hLower, hPVM⟩
  exact {
    massGap := hMassGap
    exactGapPositive := hPositive
    exactGapThreshold := hThreshold
    nonVacuumEnergyLowerBound := hLower
    firstExcitationPVMDetected := hPVM }

/-- Build the named package from the construction certificate fields only. -/
def EuclideanYangMillsInducedPipelineFullSpectralPackage.ofConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    EuclideanYangMillsInducedPipelineFullSpectralPackage S := by
  rcases
      euclidean_yang_mills_continuum_spine_certificate_only_induced_pipeline_full_spectral_package
        S C with
    ⟨hMassGap, hPositive, hThreshold, hLower, hPVM⟩
  exact {
    massGap := hMassGap
    exactGapPositive := hPositive
    exactGapThreshold := hThreshold
    nonVacuumEnergyLowerBound := hLower
    firstExcitationPVMDetected := hPVM }

/-- Build the named package from the external-audit certificate fields only. -/
def EuclideanYangMillsInducedPipelineFullSpectralPackage.ofExternalAuditCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    EuclideanYangMillsInducedPipelineFullSpectralPackage S := by
  rcases
      external_audit_readiness_euclidean_construction_spine_certificate_only_induced_pipeline_full_spectral_package
        S C with
    ⟨hMassGap, hPositive, hThreshold, hLower, hPVM⟩
  exact {
    massGap := hMassGap
    exactGapPositive := hPositive
    exactGapThreshold := hThreshold
    nonVacuumEnergyLowerBound := hLower
    firstExcitationPVMDetected := hPVM }

/-- Recover the original conjunction-shaped theorem surface from the named
package. -/
theorem EuclideanYangMillsInducedPipelineFullSpectralPackage.toConjunction
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsInducedPipelineFullSpectralPackage S) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ, E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum → δ ≤ E) ∧
    ∃ ψ : S.toPipeline.definitionBridge.spine.model.H,
      ψ ∈ S.toPipeline.definitionBridge.spine.model.spectralPVM
        ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact ⟨
    P.massGap,
    P.exactGapPositive,
    P.exactGapThreshold,
    P.nonVacuumEnergyLowerBound,
    P.firstExcitationPVMDetected⟩

end MathlibAnalytic
end MGAP4D
