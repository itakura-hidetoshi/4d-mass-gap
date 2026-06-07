import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroCountableAdditivityReduction

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Countable-additivity dichotomy for the Dirac-zero actual-Borel kernel.

For a pairwise-disjoint actual-Borel countable family, the Dirac-zero family is
reduced to exactly one of two cases: either no member contains `0`, so all
summand projections and the union projection are zero; or there is a hit index
`k`, so the union projection is the `k`-th projection and every other summand is
zero. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomy
    (F : SpectralMeasurePVMActualBorelCountableFamily) : Prop :=
  ((¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) ∧
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 ∧
    (∀ n : ℕ, spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0)) ∨
  (∃ k : ℕ,
    (0 : ℝ) ∈ (F k).1 ∧
      spectralMeasurePVMActualBorelDiracZeroProjectionMap
          (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
            spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) ∧
      (∀ n : ℕ, n ≠ k →
        spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0))

/-- Pairwise-disjoint countable families satisfy the Dirac-zero countable
additivity dichotomy. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F) :
    SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomy F := by
  classical
  by_cases hhit : ∃ n : ℕ, (0 : ℝ) ∈ (F n).1
  · rcases hhit with ⟨k, hk⟩
    right
    refine ⟨k, hk, ?_⟩
    exact spectral_measure_pvm_actual_borel_dirac_zero_countable_union_eq_hit_projection_and_zero_elsewhere
      F hdis hk
  · left
    exact ⟨
      hhit,
      spectral_measure_pvm_actual_borel_dirac_zero_no_hit_union_and_family_zero F hhit⟩

/-- Dirac-zero countable-additivity dichotomy target. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionTarget ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomy F)

/-- The Dirac-zero countable-additivity dichotomy target is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_target_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy⟩

/-- Bridge after the Dirac-zero countable-additivity dichotomy. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The bridge after the Dirac-zero countable-additivity dichotomy is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the Dirac-zero countable-additivity dichotomy. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the Dirac-zero countable-additivity dichotomy is
held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
