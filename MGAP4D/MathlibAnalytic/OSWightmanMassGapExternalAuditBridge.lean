import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge

namespace MGAP4D
namespace MathlibAnalytic

/-- External-audit projection for the fully displayed OS/Wightman → Hilbert →
Hamiltonian → PVM → mass-gap definition bridge.

This surface is intentionally parameterized by a concrete bridge `B`.  It does
not assert existence of such a Yang--Mills bridge unconditionally; it records
that once the bridge is supplied, the external audit layer sees ordinary Mathlib
propositions over the displayed gauge, Hilbert, Hamiltonian, PVM, and spectral
data. -/
def ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
    (B : OSWightmanMassGapDefinitionBridge) : Prop :=
  externalAuditReadinessGateData.ready ∧
  B.spine.axioms.gaugeGroupCompact ∧
  B.spine.axioms.gaugeGroupNontrivial ∧
  B.spine.axioms.osReflectionPositive ∧
  B.spine.axioms.wightmanLocality ∧
  B.spine.axioms.wightmanCovariance ∧
  B.spine.axioms.wightmanSpectrumCondition ∧
  B.spine.model.spacetimeDim = 4 ∧
  Nonempty B.spine.model.H ∧
  B.spine.model.hamiltonianSelfAdjoint ∧
  0 ∈ B.spine.model.energySpectrum ∧
  B.spine.model.vacuum ∈ B.spine.model.spectralPVM ({0} : Set ℝ) ∧
  (∀ E : ℝ, E ∈ B.spine.model.energySpectrum → 0 ≤ E) ∧
  (∃ δ : ℝ, 0 < δ ∧ Set.Ioo 0 δ ∩ B.spine.model.energySpectrum = ∅) ∧
  B.spine.model.firstExcitation ∈ B.spine.model.energySpectrum ∧
  0 < B.spine.model.firstExcitation ∧
  (∃ ψ : B.spine.model.H,
    ψ ∈ B.spine.model.spectralPVM ({B.spine.model.firstExcitation} : Set ℝ)) ∧
  B.spine.model.hasMassGap ∧
  0 < exactGapValueReal ∧
  exactGapValueReal = sInf (B.spine.model.energySpectrum \ ({0} : Set ℝ))

/-- The external-audit layer obtains the full OS/Wightman mass-gap definition
projection from the concrete definition bridge certificate. -/
theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection
    (B : OSWightmanMassGapDefinitionBridge) :
    ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection B := by
  unfold ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
  let C := osWightmanMassGapDefinitionBridgeCertificate B
  exact And.intro external_audit_readiness_gate_ready <|
    And.intro C.gaugeGroupCompact <|
    And.intro C.gaugeGroupNontrivial <|
    And.intro C.reflectionPositive <|
    And.intro C.locality <|
    And.intro C.covariance <|
    And.intro C.spectrumCondition <|
    And.intro C.spacetimeIsFour <|
    And.intro C.reconstructedHilbertNonempty <|
    And.intro C.hamiltonianSelfAdjoint <|
    And.intro C.vacuumEnergyZero <|
    And.intro C.vacuumSpectralPoint <|
    And.intro C.positiveEnergy <|
    And.intro C.vacuumIsolated <|
    And.intro C.firstExcitationSpectralPoint <|
    And.intro C.firstExcitationPositive <|
    And.intro C.firstExcitationPVMDetected <|
    And.intro C.massGapTheorem <|
    And.intro C.exactGapPositive C.exactGapAsSpectralThreshold

/-- The audit-visible exact-gap consequence of the OS/Wightman definition bridge. -/
theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_positive
    (B : OSWightmanMassGapDefinitionBridge) :
    0 < exactGapValueReal := by
  exact (osWightmanMassGapDefinitionBridgeCertificate B).exactGapPositive

/-- The audit-visible spectral-threshold identity of the OS/Wightman definition
bridge. -/
theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_threshold
    (B : OSWightmanMassGapDefinitionBridge) :
    exactGapValueReal = sInf (B.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact (osWightmanMassGapDefinitionBridgeCertificate B).exactGapAsSpectralThreshold

/-- The audit-visible PVM detection of the first non-vacuum spectral excitation. -/
theorem external_audit_readiness_os_wightman_definition_bridge_pvm_detects_first_excitation
    (B : OSWightmanMassGapDefinitionBridge) :
    ∃ ψ : B.spine.model.H,
      ψ ∈ B.spine.model.spectralPVM ({B.spine.model.firstExcitation} : Set ℝ) := by
  exact (osWightmanMassGapDefinitionBridgeCertificate B).firstExcitationPVMDetected

end MathlibAnalytic
end MGAP4D
