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
  exactGapPositive : 0 < exactGapValueReal
  exactGapThreshold :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
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
    limitReady := euclidean_yang_mills_continuum_spine_limit_ready S
    measureReady := euclidean_yang_mills_continuum_spine_measure_ready S
    bridgeMeasureReady :=
      euclidean_yang_mills_continuum_spine_bridge_measure_ready S
    osAxiomsReady := euclidean_yang_mills_continuum_spine_os_axioms_ready S
    unconditionalTargetReady :=
      euclidean_yang_mills_continuum_spine_unconditional_target_ready S
    osWightmanProjection :=
      external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection
        S.definitionBridge
    exactGapPositive :=
      external_audit_readiness_euclidean_construction_spine_exact_gap_positive S
    exactGapThreshold :=
      external_audit_readiness_euclidean_construction_spine_exact_gap_threshold S
    firstExcitationPVMDetected :=
      external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation S }

end MathlibAnalytic
end MGAP4D
