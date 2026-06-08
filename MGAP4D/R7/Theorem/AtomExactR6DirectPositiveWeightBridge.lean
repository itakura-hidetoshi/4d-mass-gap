import MGAP4D.R6.Theorem.ExactAtom3320DirectReviewBridge
import MGAP4D.Plaquette.ObservableSpectralWeight

namespace MGAP4D
namespace R7
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R7 bridge: the R6 direct exact-atom review lane is compatible with the
pre-Mathlib observable positive spectral-weight certificate at `33/20`.

This is a positive-weight bridge, not a final global mass-gap release.  It keeps
both surfaces visible: the R6 real-valued exact atom lane and the plaquette
positive-mass witness carried by `ObservableSpectralWeightCertificate`. -/
def AtomExactR6DirectPositiveWeightBridgeReady : Prop :=
  MGAP4D.R6.Theorem.ExactAtom3320DirectReviewBridgeReady ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.ready ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.value = 33 / 20 ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.value = 33 / 20 ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
    MGAP4D.Spectral.SpectralSector.orthogonal ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
    MGAP4D.Spectral.SpectralSector.vacuum ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  MGAP4D.R6.Theorem.ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R7 positive-weight bridge from R6 direct exact atom review is ready. -/
theorem atom_exact_r6_direct_positive_weight_bridge_ready :
    AtomExactR6DirectPositiveWeightBridgeReady := by
  exact ⟨
    MGAP4D.R6.Theorem.exact_atom_3320_direct_review_bridge_ready,
    MGAP4D.Plaquette.observable_spectral_weight_3320_certificate_ready,
    MGAP4D.Plaquette.observable_spectral_weight_3320_value,
    MGAP4D.Plaquette.observable_spectral_weight_3320_mass_value,
    MGAP4D.Plaquette.observable_spectral_weight_3320_positive_mass,
    MGAP4D.Plaquette.observable_spectral_weight_3320_witness_orthogonal,
    MGAP4D.Plaquette.observable_spectral_weight_3320_witness_not_vacuum,
    MGAP4D.R6.Theorem.exact_atom_3320_direct_review_bridge_value_eq,
    MGAP4D.R6.Theorem.exact_atom_3320_direct_review_bridge_value_mem_atom,
    MGAP4D.R6.Theorem.exact_atom_3320_direct_review_bridge_does_not_consume_positive_weight,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Projection: R7 sees the positive plaquette spectral-mass witness. -/
theorem atom_exact_r6_direct_positive_weight_bridge_positive_mass :
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  rcases atom_exact_r6_direct_positive_weight_bridge_ready with
    ⟨_hr6, _hcert, _hvalue, _hmassValue, hpos, _hortho, _hnotVacuum,
      _hrealValue, _hinAtom, _hnoConsume, _hr4⟩
  exact hpos

/-- Projection: the positive-weight bridge keeps the exact real atom value. -/
theorem atom_exact_r6_direct_positive_weight_bridge_real_value_eq :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  rcases atom_exact_r6_direct_positive_weight_bridge_ready with
    ⟨_hr6, _hcert, _hvalue, _hmassValue, _hpos, _hortho, _hnotVacuum,
      hrealValue, _hinAtom, _hnoConsume, _hr4⟩
  exact hrealValue

/-- Projection: the positive-weight bridge keeps atom membership for the exact
real value. -/
theorem atom_exact_r6_direct_positive_weight_bridge_real_value_mem_atom :
    MGAP4D.MathlibAnalytic.exactGapValueReal ∈
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom := by
  rcases atom_exact_r6_direct_positive_weight_bridge_ready with
    ⟨_hr6, _hcert, _hvalue, _hmassValue, _hpos, _hortho, _hnotVacuum,
      _hrealValue, hinAtom, _hnoConsume, _hr4⟩
  exact hinAtom

/-- Projection: the witness sits in the orthogonal sector, not the vacuum. -/
theorem atom_exact_r6_direct_positive_weight_bridge_orthogonal_nonvacuum :
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
      MGAP4D.Spectral.SpectralSector.orthogonal ∧
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
      MGAP4D.Spectral.SpectralSector.vacuum := by
  rcases atom_exact_r6_direct_positive_weight_bridge_ready with
    ⟨_hr6, _hcert, _hvalue, _hmassValue, _hpos, hortho, hnotVacuum,
      _hrealValue, _hinAtom, _hnoConsume, _hr4⟩
  exact ⟨hortho, hnotVacuum⟩

end

end Theorem
end R7
end MGAP4D
