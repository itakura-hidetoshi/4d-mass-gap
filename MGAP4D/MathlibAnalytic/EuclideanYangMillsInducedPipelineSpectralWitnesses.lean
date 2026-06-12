import MGAP4D.MathlibAnalytic.EuclideanYangMillsInducedPipelineFullSpectralPackageProvenance

namespace MGAP4D
namespace MathlibAnalytic

/-- Explicitly selected spectral witnesses extracted from an induced-pipeline
full spectral package. -/
structure EuclideanYangMillsInducedPipelineSpectralWitnesses
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  lowerBoundValue : ℝ
  lowerBoundPositive : 0 < lowerBoundValue
  lowerBoundApplies :
    ∀ E : ℝ, E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum → lowerBoundValue ≤ E
  firstExcitationWitness : S.toPipeline.definitionBridge.spine.model.H
  firstExcitationWitnessDetected :
    firstExcitationWitness ∈ S.toPipeline.definitionBridge.spine.model.spectralPVM
      ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ)

/-- Select a positive non-vacuum lower bound and a first-excitation PVM witness
from a named full spectral package. -/
noncomputable def EuclideanYangMillsInducedPipelineSpectralWitnesses.ofPackage
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsInducedPipelineFullSpectralPackage S) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S := by
  rcases P.nonVacuumEnergyLowerBound with ⟨δ, hδPositive, hLower⟩
  rcases P.firstExcitationPVMDetected with ⟨ψ, hψ⟩
  exact {
    lowerBoundValue := δ
    lowerBoundPositive := hδPositive
    lowerBoundApplies := hLower
    firstExcitationWitness := ψ
    firstExcitationWitnessDetected := hψ }

/-- Select witnesses while retaining the package provenance object as input. -/
noncomputable def
    EuclideanYangMillsInducedPipelineSpectralWitnesses.ofProvenance
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsInducedPipelineFullSpectralPackageWithProvenance S) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S :=
  EuclideanYangMillsInducedPipelineSpectralWitnesses.ofPackage P.package

/-- The selected lower-bound witness is strictly positive. -/
theorem EuclideanYangMillsInducedPipelineSpectralWitnesses.lowerBoundValue_pos
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (W : EuclideanYangMillsInducedPipelineSpectralWitnesses S) :
    0 < W.lowerBoundValue :=
  W.lowerBoundPositive

/-- The selected lower-bound witness bounds every non-vacuum pipeline energy. -/
theorem EuclideanYangMillsInducedPipelineSpectralWitnesses.lowerBoundValue_le
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (W : EuclideanYangMillsInducedPipelineSpectralWitnesses S)
    {E : ℝ}
    (hE : E ∈ S.toPipeline.nonVacuumHamiltonianSpectrum) :
    W.lowerBoundValue ≤ E :=
  W.lowerBoundApplies E hE

/-- The selected first-excitation witness is detected by the spectral PVM. -/
theorem EuclideanYangMillsInducedPipelineSpectralWitnesses.firstExcitation_mem_pvm
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (W : EuclideanYangMillsInducedPipelineSpectralWitnesses S) :
    W.firstExcitationWitness ∈
      S.toPipeline.definitionBridge.spine.model.spectralPVM
        ({S.toPipeline.definitionBridge.spine.model.firstExcitation} : Set ℝ) :=
  W.firstExcitationWitnessDetected

/-- Direct construction-spine witness extraction. -/
noncomputable def euclideanYangMillsInducedPipelineSpectralWitnesses
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S :=
  EuclideanYangMillsInducedPipelineSpectralWitnesses.ofPackage
    (euclideanYangMillsInducedPipelineFullSpectralPackage S)

/-- Construction-certificate-only witness extraction. -/
noncomputable def EuclideanYangMillsInducedPipelineSpectralWitnesses.ofConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsContinuumMeasureConstructionCertificate S) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S :=
  EuclideanYangMillsInducedPipelineSpectralWitnesses.ofPackage
    (EuclideanYangMillsInducedPipelineFullSpectralPackage.ofConstructionCertificate S C)

/-- External-audit-certificate-only witness extraction. -/
noncomputable def EuclideanYangMillsInducedPipelineSpectralWitnesses.ofExternalAuditCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    EuclideanYangMillsInducedPipelineSpectralWitnesses S :=
  EuclideanYangMillsInducedPipelineSpectralWitnesses.ofPackage
    (EuclideanYangMillsInducedPipelineFullSpectralPackage.ofExternalAuditCertificate S C)

end MathlibAnalytic
end MGAP4D
