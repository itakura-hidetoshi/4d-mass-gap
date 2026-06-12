import MGAP4D.MathlibAnalytic.AxiomaticYangMillsMassGapClosure
import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate

namespace MGAP4D
namespace MathlibAnalytic

/-- External-audit projection for the conditional OS/Wightman Yang--Mills
closure route.

This is intentionally not a `True`/receipt marker.  The projection exposes the
actual theorem consequences over a displayed Mathlib model: existence of the
mass gap, positivity of the displayed gap value, and identification of that
value with the infimum of the non-vacuum Hamiltonian spectrum. -/
def ExternalAuditReadinessAxiomaticYangMillsClosureProjection
    (M : FourDimensionalYangMillsAxiomaticModel) : Prop :=
  externalAuditReadinessGateData.ready ∧
  M.osWightman.ready ∧
  M.hasMassGap ∧
  0 < M.massGapValue ∧
  M.massGapValue = sInf (M.energySpectrum \ ({0} : Set ℝ))

/-- The external-audit gate can project the OS/Wightman conditional closure to
concrete theorem obligations over the reconstructed Hilbert/Hamiltonian/PVM
model. -/
theorem external_audit_readiness_axiomatic_yang_mills_closure_projection
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    ExternalAuditReadinessAxiomaticYangMillsClosureProjection M := by
  unfold ExternalAuditReadinessAxiomaticYangMillsClosureProjection
  rcases wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap M hOS with
    ⟨hGap, hPos, hThreshold⟩
  exact And.intro external_audit_readiness_gate_ready <|
    And.intro hOS <|
    And.intro hGap <|
    And.intro hPos hThreshold

/-- Exact-gap bridge form: if the OS/Wightman model's displayed mass-gap value
is identified with `exactGapValueReal`, then the repository's normalized exact
carrier inherits positivity and the non-vacuum spectral-threshold identity. -/
def ExternalAuditReadinessAxiomaticYangMillsExactGapProjection
    (M : FourDimensionalYangMillsAxiomaticModel) : Prop :=
  externalAuditReadinessGateData.ready ∧
  M.osWightman.ready ∧
  M.hasMassGap ∧
  M.massGapValue = exactGapValueReal ∧
  0 < exactGapValueReal ∧
  exactGapValueReal = sInf (M.energySpectrum \ ({0} : Set ℝ))

/-- External-audit exact-gap bridge theorem for the conditional OS/Wightman
route. -/
theorem external_audit_readiness_axiomatic_yang_mills_exact_gap_projection
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready)
    (hExact : M.massGapValue = exactGapValueReal) :
    ExternalAuditReadinessAxiomaticYangMillsExactGapProjection M := by
  unfold ExternalAuditReadinessAxiomaticYangMillsExactGapProjection
  rcases wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap M hOS with
    ⟨hGap, hPos, hThreshold⟩
  have hExactPos : 0 < exactGapValueReal := by
    rw [← hExact]
    exact hPos
  have hExactThreshold :
      exactGapValueReal = sInf (M.energySpectrum \ ({0} : Set ℝ)) := by
    rw [← hExact]
    exact hThreshold
  exact And.intro external_audit_readiness_gate_ready <|
    And.intro hOS <|
    And.intro hGap <|
    And.intro hExact <|
    And.intro hExactPos hExactThreshold

/-- Certificate-level theorem projection used by reviewers who want all
OS/Wightman closure outputs bundled as fields rather than as a nested
conjunction. -/
def externalAuditReadinessAxiomaticYangMillsClosureCertificate
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    AxiomaticYangMillsMassGapClosureCertificate M :=
  axiomaticYangMillsMassGapClosureCertificate M hOS

/-- The bundled certificate exposes the concrete mass-gap theorem. -/
theorem external_audit_readiness_axiomatic_certificate_mass_gap
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    (externalAuditReadinessAxiomaticYangMillsClosureCertificate M hOS).massGapTheorem := by
  exact (externalAuditReadinessAxiomaticYangMillsClosureCertificate M hOS).massGapTheorem

end MathlibAnalytic
end MGAP4D
