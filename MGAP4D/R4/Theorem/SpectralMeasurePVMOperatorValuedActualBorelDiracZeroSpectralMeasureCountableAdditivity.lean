import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroAntiCollapseGuard

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual spectral-measure interface for the Dirac-zero actual-Borel route.

This is no longer only a concrete branch/evaluator statement.  The `map` field is
the actual Dirac-zero projection map on the actual-Borel carrier, and
`countable_additive` is the spectral-measure countable-additivity law for
pairwise-disjoint countable actual-Borel families. -/
structure SpectralMeasurePVMActualBorelDiracZeroSpectralMeasure where
  map : SpectralMeasurePVMActualBorelCarrierSet → SpectralMeasurePVMActualBorelProjectionOperator
  empty_maps_to_zero : map spectralMeasurePVMActualBorelEmptySet = 0
  univ_maps_to_identity :
    map spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier
  countable_additive :
    ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
      SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
        spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
            (fun n : ℕ => map (F n)) =
          map (spectralMeasurePVMActualBorelCarrierSetIUnion F)

/-- The actual Dirac-zero spectral measure. -/
def spectralMeasurePVMActualBorelDiracZeroSpectralMeasure :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasure where
  map := spectralMeasurePVMActualBorelDiracZeroProjectionMap
  empty_maps_to_zero :=
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel.empty_maps_to_zero
  univ_maps_to_identity :=
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel.univ_maps_to_identity
  countable_additive := by
    intro F hdis
    exact spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_realizes_countable_additivity
      F hdis

/-- Countable additivity as an actual spectral-measure law, not merely as a branch
or handoff target. -/
def SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityLaw : Prop :=
  ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
          (fun n : ℕ =>
            spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.map (F n)) =
        spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.map
          (spectralMeasurePVMActualBorelCarrierSetIUnion F)

/-- The actual Dirac-zero spectral measure is countably additive. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_law :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityLaw := by
  intro F hdis
  exact spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.countable_additive F hdis

/-- The Dirac-zero countable-additivity result is closed at the actual spectral
measure interface. -/
def SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityClosed : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSafeUseTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero actual spectral-measure countable-additivity law is closed. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_closed :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityClosed := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_law,
    spectral_measure_pvm_actual_borel_dirac_zero_safe_use_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after closing countable additivity at the actual spectral
measure interface. -/
def SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityClosed ∧
  SpectralMeasurePVMActualBorelDiracZeroSafeUsePublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after closing actual spectral-measure countable additivity
is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_closed,
    spectral_measure_pvm_actual_borel_dirac_zero_safe_use_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
