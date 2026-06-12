import MGAP4D.MathlibAnalytic.AxiomaticYangMillsExternalAuditProjection

namespace MGAP4D
namespace MathlibAnalytic

/-- A reconstruction spine connecting an OS/Wightman axiom package to the
reconstructed Hilbert/Hamiltonian/PVM model used by the mass-gap closure.

This is the next hard-interface target: a concrete Yang--Mills construction
should fill `axioms`, `model`, and the identity showing that the reconstructed
model is built from exactly those axioms.  The downstream theorems then project
ordinary Mathlib statements rather than terminal receipts. -/
structure OSWightmanHamiltonianReconstructionSpine where
  axioms : OSWightmanYangMillsAxioms
  model : FourDimensionalYangMillsAxiomaticModel
  model_uses_axioms : model.osWightman = axioms
  axioms_ready : axioms.ready
  exact_gap_value_identified : model.massGapValue = exactGapValueReal

/-- The model-side OS/Wightman readiness transported along the reconstruction
identity. -/
theorem os_wightman_reconstruction_model_ready
    (S : OSWightmanHamiltonianReconstructionSpine) :
    S.model.osWightman.ready := by
  rw [S.model_uses_axioms]
  exact S.axioms_ready

/-- The reconstruction spine projects to a positive mass-gap theorem over the
reconstructed Hilbert/Hamiltonian/PVM model. -/
theorem os_wightman_reconstruction_spine_has_mass_gap
    (S : OSWightmanHamiltonianReconstructionSpine) :
    S.model.hasMassGap := by
  exact axiomatic_yang_mills_derives_positive_mass_gap S.model
    (os_wightman_reconstruction_model_ready S)

/-- The reconstruction spine proves positivity of the repository's normalized
exact gap carrier once the reconstructed model identifies its spectral gap value
with `exactGapValueReal`. -/
theorem os_wightman_reconstruction_spine_exact_gap_positive
    (S : OSWightmanHamiltonianReconstructionSpine) :
    0 < exactGapValueReal := by
  have hModelPos : 0 < S.model.massGapValue :=
    axiomatic_yang_mills_mass_gap_value_positive S.model
      (os_wightman_reconstruction_model_ready S)
  rw [← S.exact_gap_value_identified]
  exact hModelPos

/-- The reconstruction spine identifies `exactGapValueReal` with the first
non-vacuum Hamiltonian spectral threshold. -/
theorem os_wightman_reconstruction_spine_exact_gap_is_sInf_nonvacuum
    (S : OSWightmanHamiltonianReconstructionSpine) :
    exactGapValueReal = sInf (S.model.energySpectrum \ ({0} : Set ℝ)) := by
  have hModelThreshold :
      S.model.massGapValue = sInf (S.model.energySpectrum \ ({0} : Set ℝ)) :=
    axiomatic_yang_mills_mass_gap_value_eq_sInf_nonvacuum S.model
      (os_wightman_reconstruction_model_ready S)
  rw [← S.exact_gap_value_identified]
  exact hModelThreshold

/-- External-audit exact-gap theorem projected from the reconstruction spine.
This is the direct bridge from OS/Wightman reconstruction to the audit-visible
exact-gap carrier. -/
theorem os_wightman_reconstruction_spine_external_exact_gap_projection
    (S : OSWightmanHamiltonianReconstructionSpine) :
    ExternalAuditReadinessAxiomaticYangMillsExactGapProjection S.model := by
  exact external_audit_readiness_axiomatic_yang_mills_exact_gap_projection
    S.model
    (os_wightman_reconstruction_model_ready S)
    S.exact_gap_value_identified

/-- Bundle all theorem-level outputs of the reconstruction spine. -/
structure OSWightmanHamiltonianReconstructionSpineCertificate
    (S : OSWightmanHamiltonianReconstructionSpine) where
  modelReady : S.model.osWightman.ready
  massGapTheorem : S.model.hasMassGap
  exactGapPositive : 0 < exactGapValueReal
  exactGapAsSpectralThreshold :
    exactGapValueReal = sInf (S.model.energySpectrum \ ({0} : Set ℝ))
  externalAuditProjection :
    ExternalAuditReadinessAxiomaticYangMillsExactGapProjection S.model

/-- Construct the certificate without `True`, `ready` receipts, or bare markers:
each field is a theorem over the reconstructed model. -/
def osWightmanHamiltonianReconstructionSpineCertificate
    (S : OSWightmanHamiltonianReconstructionSpine) :
    OSWightmanHamiltonianReconstructionSpineCertificate S :=
  { modelReady := os_wightman_reconstruction_model_ready S
    massGapTheorem := os_wightman_reconstruction_spine_has_mass_gap S
    exactGapPositive := os_wightman_reconstruction_spine_exact_gap_positive S
    exactGapAsSpectralThreshold :=
      os_wightman_reconstruction_spine_exact_gap_is_sInf_nonvacuum S
    externalAuditProjection :=
      os_wightman_reconstruction_spine_external_exact_gap_projection S }

end MathlibAnalytic
end MGAP4D
