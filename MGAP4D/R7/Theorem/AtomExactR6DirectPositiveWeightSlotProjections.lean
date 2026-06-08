import MGAP4D.R7.Theorem.AtomExactR6DirectPositiveWeightSlotClosure

namespace MGAP4D
namespace R7
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Projection: the closed R7 review slot carries positive spectral mass. -/
theorem atom_exact_r6_direct_positive_weight_review_surface_positive_mass :
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  rcases atom_exact_r6_direct_positive_weight_review_surface_closed with
    ⟨_hbridge, hpositive, _hvalue, _hmem, _hortho, _hnotVacuum⟩
  exact hpositive

/-- Projection: the closed R7 review slot carries the exact real value `33/20`. -/
theorem atom_exact_r6_direct_positive_weight_review_surface_real_value_eq :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  rcases atom_exact_r6_direct_positive_weight_review_surface_closed with
    ⟨_hbridge, _hpositive, hvalue, _hmem, _hortho, _hnotVacuum⟩
  exact hvalue

/-- Projection: the closed R7 review slot keeps membership in the singleton atom. -/
theorem atom_exact_r6_direct_positive_weight_review_surface_real_value_mem_atom :
    MGAP4D.MathlibAnalytic.exactGapValueReal ∈
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom := by
  rcases atom_exact_r6_direct_positive_weight_review_surface_closed with
    ⟨_hbridge, _hpositive, _hvalue, hmem, _hortho, _hnotVacuum⟩
  exact hmem

/-- Projection: the closed R7 review slot places the witness in the orthogonal,
non-vacuum sector. -/
theorem atom_exact_r6_direct_positive_weight_review_surface_orthogonal_nonvacuum :
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
      MGAP4D.Spectral.SpectralSector.orthogonal ∧
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
      MGAP4D.Spectral.SpectralSector.vacuum := by
  rcases atom_exact_r6_direct_positive_weight_review_surface_closed with
    ⟨_hbridge, _hpositive, _hvalue, _hmem, hortho, hnotVacuum⟩
  exact ⟨hortho, hnotVacuum⟩

/-- Bundled payload extracted from the closed R7 positive-weight review slot. -/
theorem atom_exact_r6_direct_positive_weight_review_surface_payload :
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
    MGAP4D.MathlibAnalytic.exactGapValueReal ∈
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
    MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
        MGAP4D.Spectral.SpectralSector.orthogonal ∧
      MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
        MGAP4D.Spectral.SpectralSector.vacuum := by
  exact ⟨
    atom_exact_r6_direct_positive_weight_review_surface_positive_mass,
    atom_exact_r6_direct_positive_weight_review_surface_real_value_eq,
    atom_exact_r6_direct_positive_weight_review_surface_real_value_mem_atom,
    atom_exact_r6_direct_positive_weight_review_surface_orthogonal_nonvacuum⟩

end

end Theorem
end R7
end MGAP4D
