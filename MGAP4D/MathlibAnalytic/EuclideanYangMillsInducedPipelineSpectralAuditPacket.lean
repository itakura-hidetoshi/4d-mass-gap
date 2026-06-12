import MGAP4D.MathlibAnalytic.EuclideanYangMillsInducedPipelineSpectralWitnessesProvenance

namespace MGAP4D
namespace MathlibAnalytic

/-- Audit packet combining the provenanced full spectral package and the
provenanced extracted witnesses on the induced Euclidean measure-to-mass-gap
pipeline.

This packet is wrapper-only: it introduces no new mathematical authority and
records source agreement between the package and witness layers. -/
structure EuclideanYangMillsInducedPipelineSpectralAuditPacket
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  source : EuclideanYangMillsInducedPipelineFullSpectralPackageSource
  packageWithProvenance :
    EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S
  witnessesWithProvenance :
    EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance S
  packageSource_eq : packageWithProvenance.source = source
  witnessSource_eq : witnessesWithProvenance.source = source

/-- Build an audit packet from a provenanced full spectral package. -/
noncomputable def EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofPackageProvenance
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S) :
    EuclideanYangMillsInducedPipelineSpectralAuditPacket S :=
  { source := P.source
    packageWithProvenance := P
    witnessesWithProvenance :=
      EuclideanYangMillsInducedPipelineSpectralWitnessesWithProvenance.ofPackageProvenance P
    packageSource_eq := rfl
    witnessSource_eq := rfl }

/-- Direct construction-spine audit packet. -/
noncomputable def euclideanYangMillsInducedPipelineSpectralAuditPacket
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsInducedPipelineSpectralAuditPacket S :=
  EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofPackageProvenance
    (euclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S)

/-- Construction-certificate-only audit packet. -/
noncomputable def EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    EuclideanYangMillsInducedPipelineSpectralAuditPacket S :=
  EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofPackageProvenance
    (EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofConstructionCertificate
      S C)

/-- External-audit-certificate-only audit packet. -/
noncomputable def EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofExternalAuditCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    EuclideanYangMillsInducedPipelineSpectralAuditPacket S :=
  EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofPackageProvenance
    (EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance.ofExternalAuditCertificate
      S C)

/-- Package and witness provenance sources agree inside every audit packet. -/
theorem EuclideanYangMillsInducedPipelineSpectralAuditPacket.source_consistent
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (A : EuclideanYangMillsInducedPipelineSpectralAuditPacket S) :
    A.packageWithProvenance.source = A.witnessesWithProvenance.source := by
  rw [A.packageSource_eq, A.witnessSource_eq]

/-- Recover the named full spectral package from the audit packet. -/
def EuclideanYangMillsInducedPipelineSpectralAuditPacket.package
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (A : EuclideanYangMillsInducedPipelineSpectralAuditPacket S) :
    EuclideanYangMillsInducedPipelineFullSpectralPackage S :=
  A.packageWithProvenance.package

/-- Recover the selected spectral witnesses from the audit packet. -/
def EuclideanYangMillsInducedPipelineSpectralAuditPacket.witnesses
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (A : EuclideanYangMillsInducedPipelineSpectralAuditPacket S) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S :=
  A.witnessesWithProvenance.witnesses

/-- Recover the original conjunction-shaped theorem surface from the audit
packet. -/
theorem EuclideanYangMillsInducedPipelineSpectralAuditPacket.toConjunction
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (A : EuclideanYangMillsInducedPipelineSpectralAuditPacket S) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ, E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum → δ ≤ E) ∧
    ∃ ψ : S.toPipeline.definitionBridge.spine.model.H,
      ψ ∈ S.toPipeline.definitionBridge.spine.model.spectralPVM
        ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact A.packageWithProvenance.toConjunction

@[simp] theorem euclidean_yang_mills_induced_pipeline_spectral_audit_packet_direct_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsInducedPipelineSpectralAuditPacket S).source =
      .constructionSpine := by
  rfl

@[simp] theorem euclidean_yang_mills_induced_pipeline_spectral_audit_packet_construction_certificate_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    (EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofConstructionCertificate S C).source =
      .constructionCertificate := by
  rfl

@[simp] theorem euclidean_yang_mills_induced_pipeline_spectral_audit_packet_external_audit_certificate_source
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    (EuclideanYangMillsInducedPipelineSpectralAuditPacket.ofExternalAuditCertificate S C).source =
      .externalAuditCertificate := by
  rfl

end MathlibAnalytic
end MGAP4D
