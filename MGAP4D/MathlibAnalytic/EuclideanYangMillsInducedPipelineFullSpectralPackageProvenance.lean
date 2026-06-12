import MGAP4D.MathlibAnalytic.EuclideanYangMillsInducedPipelineFullSpectralPackage

namespace MGAP4D
namespace MathlibAnalytic

/-- Audit-visible source of an induced-pipeline full spectral package. -/
inductive EuclideanYangMillsInducedPipelineFullSpectralPackageSource where
  | constructionSpine
  | constructionCertificate
  | externalAuditCertificate
  deriving DecidableEq, Repr

/-- A full induced-pipeline spectral package together with its construction
provenance.  The source tag does not strengthen the mathematical claim; it records
which theorem/certificate surface supplied the package. -/
structure EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  source : EuclideanYangMillsInducedPipelineFullSpectralPackageSource
  package : EuclideanYangMillsInducedPipelineFullSpectralPackage S

/-- Record direct construction-spine provenance. -/
def euclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S :=
  { source := .constructionSpine
    package := euclideanYangMillsInducedPipelineFullSpectralPackage S }

/-- Record construction-certificate-only provenance. -/
def EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S :=
  { source := .constructionCertificate
    package :=
      EuclideanYangMillsInducedPipelineFullSpectralPackage.ofConstructionCertificate S C }

/-- Record external-audit-certificate-only provenance. -/
def EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofExternalAuditCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S :=
  { source := .externalAuditCertificate
    package :=
      EuclideanYangMillsInducedPipelineFullSpectralPackage.ofExternalAuditCertificate S C }

@[simp] theorem euclidean_yang_mills_induced_pipeline_full_spectral_package_direct_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S).source =
      .constructionSpine := by
  rfl

@[simp] theorem euclidean_yang_mills_induced_pipeline_full_spectral_package_construction_certificate_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    (EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofConstructionCertificate
      S C).source = .constructionCertificate := by
  rfl

@[simp] theorem euclidean_yang_mills_induced_pipeline_full_spectral_package_external_audit_certificate_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    (EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofExternalAuditCertificate
      S C).source = .externalAuditCertificate := by
  rfl

/-- Forget provenance and recover the original conjunction-shaped theorem
surface. -/
theorem EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.toConjunction
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ, E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum → δ ≤ E) ∧
    ∃ ψ : S.toPipeline.definitionBridge.spine.model.H,
      ψ ∈ S.toPipeline.definitionBridge.spine.model.spectralPVM
        ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact P.package.toConjunction

end MathlibAnalytic
end MGAP4D
