import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge
import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine

namespace MGAP4D
namespace MathlibAnalytic

/-- External-audit projection for the finite-volume/continuum Euclidean
Yang--Mills construction spine.

This projection does not assert that the construction spine exists
unconditionally.  It states that once such a spine is supplied, its induced
OS/Wightman definition bridge lands in the existing external-audit readiness
projection. -/
def ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
  S.limitReady ∧
  S.measurePackage.ready ∧
  S.bridge.measure.ready ∧
  S.definitionBridge.spine.axioms.ready ∧
  S.toUnconditionalTarget.ready ∧
  ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
    S.definitionBridge

/-- The finite-volume/continuum construction spine projects into the external
audit readiness surface for the OS/Wightman mass-gap definition bridge. -/
theorem external_audit_readiness_euclidean_yang_mills_construction_spine_projection
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection S := by
  unfold ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
  exact ⟨
    euclidean_yang_mills_continuum_spine_limit_ready S,
    euclidean_yang_mills_continuum_spine_measure_ready S,
    euclidean_yang_mills_continuum_spine_bridge_measure_ready S,
    euclidean_yang_mills_continuum_spine_os_axioms_ready S,
    euclidean_yang_mills_continuum_spine_unconditional_target_ready S,
    external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection
      S.definitionBridge⟩

/-- The construction-spine external-audit projection exposes limit readiness. -/
theorem external_audit_readiness_euclidean_construction_spine_projection_limit_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.limitReady := by
  rcases external_audit_readiness_euclidean_yang_mills_construction_spine_projection S with
    ⟨hLimit, hMeasure, hBridgeMeasure, hOSAxioms, hTarget, hOSWightman⟩
  exact hLimit

/-- The construction-spine external-audit projection exposes readiness of the
continuum Euclidean measure package. -/
theorem external_audit_readiness_euclidean_construction_spine_projection_measure_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.measurePackage.ready := by
  rcases external_audit_readiness_euclidean_yang_mills_construction_spine_projection S with
    ⟨hLimit, hMeasure, hBridgeMeasure, hOSAxioms, hTarget, hOSWightman⟩
  exact hMeasure

/-- The construction-spine external-audit projection exposes readiness of the
measure package used by its OS/Wightman bridge. -/
theorem external_audit_readiness_euclidean_construction_spine_projection_bridge_measure_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.bridge.measure.ready := by
  rcases external_audit_readiness_euclidean_yang_mills_construction_spine_projection S with
    ⟨hLimit, hMeasure, hBridgeMeasure, hOSAxioms, hTarget, hOSWightman⟩
  exact hBridgeMeasure

/-- The construction-spine external-audit projection exposes readiness of the
OS/Wightman axioms used by the downstream definition bridge. -/
theorem external_audit_readiness_euclidean_construction_spine_projection_os_axioms_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.ready := by
  rcases external_audit_readiness_euclidean_yang_mills_construction_spine_projection S with
    ⟨hLimit, hMeasure, hBridgeMeasure, hOSAxioms, hTarget, hOSWightman⟩
  exact hOSAxioms

/-- The construction-spine external-audit projection exposes readiness of the
induced unconditional Euclidean-measure construction target. -/
theorem external_audit_readiness_euclidean_construction_spine_projection_unconditional_target_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toUnconditionalTarget.ready := by
  rcases external_audit_readiness_euclidean_yang_mills_construction_spine_projection S with
    ⟨hLimit, hMeasure, hBridgeMeasure, hOSAxioms, hTarget, hOSWightman⟩
  exact hTarget

/-- The construction-spine external-audit projection exposes the underlying
OS/Wightman mass-gap definition bridge projection. -/
theorem external_audit_readiness_euclidean_construction_spine_projection_os_wightman_bridge
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
      S.definitionBridge := by
  rcases external_audit_readiness_euclidean_yang_mills_construction_spine_projection S with
    ⟨hLimit, hMeasure, hBridgeMeasure, hOSAxioms, hTarget, hOSWightman⟩
  exact hOSWightman

/-- The construction spine has the external-audit exact-gap positivity consequence. -/
theorem external_audit_readiness_euclidean_construction_spine_exact_gap_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal := by
  exact external_audit_readiness_os_wightman_definition_bridge_exact_gap_positive
    S.definitionBridge

/-- The construction spine has the external-audit spectral-threshold identity. -/
theorem external_audit_readiness_euclidean_construction_spine_exact_gap_threshold
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact external_audit_readiness_os_wightman_definition_bridge_exact_gap_threshold
    S.definitionBridge

/-- The construction spine has the external-audit PVM detection of the first
non-vacuum excitation. -/
theorem external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact external_audit_readiness_os_wightman_definition_bridge_pvm_detects_first_excitation
    S.definitionBridge

/-- The construction spine exposes a positive lower bound for all non-vacuum
spectral energies at the external-audit surface. -/
theorem external_audit_readiness_euclidean_construction_spine_nonvacuum_energy_lower_bound
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E := by
  exact euclidean_yang_mills_continuum_spine_nonvacuum_energy_lower_bound S

/-- External-audit theorem package: from the construction spine, the mass-gap
predicate, exact positivity, threshold identity, and PVM first-excitation
detection are available together. -/
theorem external_audit_readiness_euclidean_construction_spine_mass_gap_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact ⟨
    euclidean_yang_mills_continuum_spine_mass_gap_definition S,
    external_audit_readiness_euclidean_construction_spine_exact_gap_positive S,
    external_audit_readiness_euclidean_construction_spine_exact_gap_threshold S,
    external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation S⟩

/-- External-audit certificate collecting the construction-spine readiness,
OS/Wightman projection, and exact spectral consequences. -/
structure ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  projection : ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection S
  limitReady : S.limitReady
  measureReady : S.measurePackage.ready
  bridgeMeasureReady : S.bridge.measure.ready
  osAxiomsReady : S.definitionBridge.spine.axioms.ready
  unconditionalTargetReady : S.toUnconditionalTarget.ready
  osWightmanProjection :
    ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
      S.definitionBridge
  massGapDefinition : S.definitionBridge.spine.model.hasMassGap
  exactGapPositive : 0 < exactGapValueReal
  exactGapThreshold :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
  nonVacuumEnergyLowerBound :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E
  firstExcitationPVMDetected :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)

/-- Build the external-audit certificate for the finite-volume/continuum
construction spine. -/
def externalAuditReadinessEuclideanYangMillsConstructionSpineCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S :=
  { projection :=
      external_audit_readiness_euclidean_yang_mills_construction_spine_projection S
    limitReady :=
      external_audit_readiness_euclidean_construction_spine_projection_limit_ready S
    measureReady :=
      external_audit_readiness_euclidean_construction_spine_projection_measure_ready S
    bridgeMeasureReady :=
      external_audit_readiness_euclidean_construction_spine_projection_bridge_measure_ready S
    osAxiomsReady :=
      external_audit_readiness_euclidean_construction_spine_projection_os_axioms_ready S
    unconditionalTargetReady :=
      external_audit_readiness_euclidean_construction_spine_projection_unconditional_target_ready S
    osWightmanProjection :=
      external_audit_readiness_euclidean_construction_spine_projection_os_wightman_bridge S
    massGapDefinition :=
      (external_audit_readiness_euclidean_construction_spine_mass_gap_package S).1
    exactGapPositive :=
      (external_audit_readiness_euclidean_construction_spine_mass_gap_package S).2.1
    exactGapThreshold :=
      (external_audit_readiness_euclidean_construction_spine_mass_gap_package S).2.2.1
    nonVacuumEnergyLowerBound :=
      external_audit_readiness_euclidean_construction_spine_nonvacuum_energy_lower_bound S
    firstExcitationPVMDetected :=
      (external_audit_readiness_euclidean_construction_spine_mass_gap_package S).2.2.2 }

/-- A certificate can be consumed as the same external-audit readiness package.
This theorem is useful for downstream files that receive only the certificate
record rather than the original construction spine. -/
theorem external_audit_readiness_euclidean_construction_spine_certificate_readiness_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    S.limitReady ∧
    S.measurePackage.ready ∧
    S.bridge.measure.ready ∧
    S.definitionBridge.spine.axioms.ready ∧
    S.toUnconditionalTarget.ready ∧
    ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
      S.definitionBridge := by
  exact ⟨
    C.limitReady,
    C.measureReady,
    C.bridgeMeasureReady,
    C.osAxiomsReady,
    C.unconditionalTargetReady,
    C.osWightmanProjection⟩

/-- A certificate can be consumed as the external-audit lower-bound package for
non-vacuum spectral energies. -/
theorem external_audit_readiness_euclidean_construction_spine_certificate_nonvacuum_energy_lower_bound
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E := by
  exact C.nonVacuumEnergyLowerBound

/-- A certificate can be consumed as the same external-audit mass-gap package.
This theorem is useful for downstream files that receive only the certificate
record rather than the original construction spine. -/
theorem external_audit_readiness_euclidean_construction_spine_certificate_mass_gap_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    S.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact ⟨
    C.massGapDefinition,
    C.exactGapPositive,
    C.exactGapThreshold,
    C.firstExcitationPVMDetected⟩

/-- A certificate can be consumed as the full external-audit spectral package:
mass-gap predicate, exact-gap positivity, threshold identity, non-vacuum lower
bound, and first-excitation PVM detection. -/
theorem external_audit_readiness_euclidean_construction_spine_certificate_full_spectral_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    S.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E) ∧
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact ⟨
    C.massGapDefinition,
    C.exactGapPositive,
    C.exactGapThreshold,
    C.nonVacuumEnergyLowerBound,
    C.firstExcitationPVMDetected⟩

/-- A construction-spine certificate also consumes as the induced Euclidean
measure-to-mass-gap pipeline theorem.  This connects the external-audit
certificate back to the original `S.toPipeline` theorem surface. -/
theorem external_audit_readiness_euclidean_construction_spine_certificate_induced_pipeline_mass_gap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (_C : ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate S) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact euclidean_yang_mills_finite_volume_continuum_construction_mass_gap S

end MathlibAnalytic
end MGAP4D
