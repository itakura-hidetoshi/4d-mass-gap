import MGAP4D.R4.Theorem.SpectralMeasurePVMCandidateConstruction

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Exact atom of the R4 PVM candidate is the singleton exact-gap atom. -/
theorem spectral_measure_pvm_candidate_exact_atom_eq_singleton :
    spectralMeasurePVMCandidateConstruction.exactAtom =
      Set.singleton MathlibAnalytic.exactGapValueReal := by
  exact spectralMeasurePVMCandidateConstruction.exactAtom_eq_singleton

/-- The exact gap value lies in the R4 candidate atom. -/
theorem spectral_measure_pvm_candidate_exact_value_mem_atom :
    MathlibAnalytic.exactGapValueReal ∈
      spectralMeasurePVMCandidateConstruction.exactAtom := by
  exact spectralMeasurePVMCandidateConstruction.exactValueInAtom

/-- The R4 candidate projection mass is the analytic-spine prototype mass. -/
theorem spectral_measure_pvm_candidate_projection_mass_eq :
    spectralMeasurePVMCandidateConstruction.projectionMass =
      MathlibAnalytic.prototypeProjectionMassReal := by
  exact spectralMeasurePVMCandidateConstruction.projectionMass_eq

/-- The exact atom has positive candidate projection mass. -/
theorem spectral_measure_pvm_candidate_exact_atom_mass_positive :
    0 < spectralMeasurePVMCandidateConstruction.projectionMass
      spectralMeasurePVMCandidateConstruction.exactAtom := by
  exact spectralMeasurePVMCandidateConstruction.exactAtomMassPositive

/-- The exact atom has nonzero candidate projection mass. -/
theorem spectral_measure_pvm_candidate_exact_atom_mass_nonzero :
    spectralMeasurePVMCandidateConstruction.projectionMass
      spectralMeasurePVMCandidateConstruction.exactAtom ≠ 0 := by
  exact spectralMeasurePVMCandidateConstruction.exactAtomMassNonzero

/-- The R4 candidate retains the exact value `33 / 20`. -/
theorem spectral_measure_pvm_candidate_exact_value_eq_3320 :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact spectralMeasurePVMCandidateConstruction.exactValueEq3320

/-- The spectral projection-at-exact surface is available for the R4 candidate. -/
theorem spectral_measure_pvm_candidate_projection_at_exact :
    MathlibAnalytic.prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact := by
  exact spectralMeasurePVMCandidateConstruction.spectralProjectionAtExact

/-- The R4 PVM candidate has been constructed. -/
theorem spectral_measure_pvm_candidate_pvm_constructed :
    spectralMeasurePVMCandidateConstruction.pvmCandidateConstructed := by
  exact spectralMeasurePVMCandidateConstruction.pvmCandidateConstructed

/-- The R4 spectral-measure candidate has been constructed. -/
theorem spectral_measure_candidate_constructed :
    spectralMeasurePVMCandidateConstruction.spectralMeasureCandidateConstructed := by
  exact spectralMeasurePVMCandidateConstruction.spectralMeasureCandidateConstructed

/-- The full PVM theorem is still intentionally open at this candidate-law layer. -/
theorem spectral_measure_pvm_candidate_full_pvm_theorem_still_open :
    spectralMeasurePVMCandidateConstruction.fullPVMTheoremStillOpen := by
  exact spectralMeasurePVMCandidateConstruction.fullPVMTheoremStillOpen

/-- Countable additivity is still intentionally open at this candidate-law layer. -/
theorem spectral_measure_pvm_candidate_countable_additivity_still_open :
    spectralMeasurePVMCandidateConstruction.countableAdditivityStillOpen := by
  exact spectralMeasurePVMCandidateConstruction.countableAdditivityStillOpen

/-- Full projection-valuedness is still intentionally open at this candidate-law layer. -/
theorem spectral_measure_pvm_candidate_projection_valuedness_still_open :
    spectralMeasurePVMCandidateConstruction.projectionValuednessStillOpen := by
  exact spectralMeasurePVMCandidateConstruction.projectionValuednessStillOpen

/-- The concrete spectral theorem is still intentionally open at this candidate-law layer. -/
theorem spectral_measure_pvm_candidate_concrete_spectral_theorem_still_open :
    spectralMeasurePVMCandidateConstruction.concreteSpectralTheoremStillOpen := by
  exact spectralMeasurePVMCandidateConstruction.concreteSpectralTheoremStillOpen

/-- R4 candidate law bundle.

This law bundle is the reusable surface for downstream R4 work: exact atom,
projection mass, positivity, nonzero mass, and projection-at-exact are available
as theorems, while full PVM axioms remain explicitly open. -/
def SpectralMeasurePVMCandidateLawBundleReady : Prop :=
  spectralMeasurePVMCandidateConstruction.ready ∧
  spectralMeasurePVMCandidateConstruction.exactAtom =
    Set.singleton MathlibAnalytic.exactGapValueReal ∧
  MathlibAnalytic.exactGapValueReal ∈
    spectralMeasurePVMCandidateConstruction.exactAtom ∧
  spectralMeasurePVMCandidateConstruction.projectionMass =
    MathlibAnalytic.prototypeProjectionMassReal ∧
  0 < spectralMeasurePVMCandidateConstruction.projectionMass
    spectralMeasurePVMCandidateConstruction.exactAtom ∧
  spectralMeasurePVMCandidateConstruction.projectionMass
    spectralMeasurePVMCandidateConstruction.exactAtom ≠ 0 ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MathlibAnalytic.prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact ∧
  spectralMeasurePVMCandidateConstruction.pvmCandidateConstructed ∧
  spectralMeasurePVMCandidateConstruction.spectralMeasureCandidateConstructed ∧
  spectralMeasurePVMCandidateConstruction.fullPVMTheoremStillOpen ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityStillOpen ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessStillOpen ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralTheoremStillOpen

/-- The R4 candidate law bundle is ready. -/
theorem spectral_measure_pvm_candidate_law_bundle_ready :
    SpectralMeasurePVMCandidateLawBundleReady := by
  exact ⟨
    spectral_measure_pvm_candidate_construction_ready,
    spectral_measure_pvm_candidate_exact_atom_eq_singleton,
    spectral_measure_pvm_candidate_exact_value_mem_atom,
    spectral_measure_pvm_candidate_projection_mass_eq,
    spectral_measure_pvm_candidate_exact_atom_mass_positive,
    spectral_measure_pvm_candidate_exact_atom_mass_nonzero,
    spectral_measure_pvm_candidate_exact_value_eq_3320,
    spectral_measure_pvm_candidate_projection_at_exact,
    spectral_measure_pvm_candidate_pvm_constructed,
    spectral_measure_candidate_constructed,
    spectral_measure_pvm_candidate_full_pvm_theorem_still_open,
    spectral_measure_pvm_candidate_countable_additivity_still_open,
    spectral_measure_pvm_candidate_projection_valuedness_still_open,
    spectral_measure_pvm_candidate_concrete_spectral_theorem_still_open⟩

/-- R4 candidate law boundary.

The finite exact-atom law bundle is now closed.  The remaining proof tasks are
precisely the full PVM axioms and concrete spectral theorem. -/
def SpectralMeasurePVMCandidateLawBoundary : Prop :=
  SpectralMeasurePVMCandidateLawBundleReady ∧
  spectralMeasurePVMCandidateConstruction.fullPVMTheoremStillOpen ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityStillOpen ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessStillOpen ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralTheoremStillOpen

/-- The R4 candidate law boundary is ready. -/
theorem spectral_measure_pvm_candidate_law_boundary_ready :
    SpectralMeasurePVMCandidateLawBoundary := by
  exact ⟨
    spectral_measure_pvm_candidate_law_bundle_ready,
    spectral_measure_pvm_candidate_full_pvm_theorem_still_open,
    spectral_measure_pvm_candidate_countable_additivity_still_open,
    spectral_measure_pvm_candidate_projection_valuedness_still_open,
    spectral_measure_pvm_candidate_concrete_spectral_theorem_still_open⟩

end

end Theorem
end R4
end MGAP4D