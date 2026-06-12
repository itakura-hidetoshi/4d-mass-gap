import MGAP4D.MathlibAnalytic.EuclideanYangMillsInducedPipelineSpectralWitnesses

namespace MGAP4D
namespace MathlibAnalytic

/-- Explicit spectral witnesses together with the provenance of the package from
which they were extracted. -/
structure EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  source : EuclideanYangMillsInducedPipelineFullSpectralPackageSource
  witnesses : EuclideanYangMillsInducedPipelineSpectralWitnesses S

/-- Preserve provenance while extracting witnesses from a provenanced package. -/
noncomputable def
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofPackageProvenance
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S) :
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S :=
  { source := P.source
    witnesses := EuclideanYangMillsInducedPipelineSpectralWitnesses.ofProvenance P }

/-- Direct construction-spine witness extraction with provenance. -/
noncomputable def euclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S :=
  EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofPackageProvenance
    (euclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S)

/-- Construction-certificate-only witness extraction with provenance. -/
noncomputable def
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S :=
  EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofPackageProvenance
    (EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofConstructionCertificate
      S C)

/-- External-audit-certificate-only witness extraction with provenance. -/
noncomputable def
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofExternalAuditCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S :=
  EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofPackageProvenance
    (EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofExternalAuditCertificate
      S C)

@[simp] theorem euclidean_yang_mills_induced_pipeline_spectral_witnesses_direct_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S).source =
      .constructionSpine := by
  rfl

@[simp] theorem euclidean_yang_mills_induced_pipeline_spectral_witnesses_construction_certificate_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    (EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofConstructionCertificate
      S C).source = .constructionCertificate := by
  rfl

@[simp] theorem euclidean_yang_mills_induced_pipeline_spectral_witnesses_external_audit_certificate_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    (EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofExternalAuditCertificate
      S C).source = .externalAuditCertificate := by
  rfl

/-- Forget provenance and recover the selected witnesses. -/
def EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.forget
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (W : EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S :=
  W.witnesses

end MathlibAnalytic
end MGAP4D
