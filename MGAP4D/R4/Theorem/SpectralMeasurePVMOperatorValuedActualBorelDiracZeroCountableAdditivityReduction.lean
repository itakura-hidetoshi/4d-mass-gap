import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroCountableSupport
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelRecursiveFinitePartialUnion

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Away from a hit index, a pairwise-disjoint Dirac-zero family maps to zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_zero_away_from_hit
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {k : ℕ}
    (hk : (0 : ℝ) ∈ (F k).1) :
    ∀ n : ℕ, n ≠ k →
      spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0 := by
  intro n hne
  exact spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_other_projection_zero
    F hdis hk hne

/-- If a pairwise-disjoint family has a hit at `k`, then the countable-union
projection is the `k`-th projection and all other family projections are zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_union_eq_hit_projection_and_zero_elsewhere
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {k : ℕ}
    (hk : (0 : ℝ) ∈ (F k).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
      (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
        spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) ∧
    (∀ n : ℕ, n ≠ k →
      spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0) := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_eq_hit_projection
      F hdis hk,
    spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_zero_away_from_hit
      F hdis hk⟩

/-- If no family member contains `0`, then every family projection is zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_no_hit_all_projections_zero
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hno : ¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) :
    ∀ n : ℕ, spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0 := by
  classical
  intro n
  have hnot : (0 : ℝ) ∉ (F n).1 := by
    intro hn
    exact hno ⟨n, hn⟩
  simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hnot]

/-- If no family member contains `0`, then the countable-union projection and all
family projections are zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_no_hit_union_and_family_zero
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hno : ¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 ∧
    (∀ n : ℕ, spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0) := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_zero_of_no_hit F hno,
    spectral_measure_pvm_actual_borel_dirac_zero_no_hit_all_projections_zero F hno⟩

/-- Support-reduction target for Dirac-zero countable additivity. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableSupportLawTarget ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    (¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) →
      spectralMeasurePVMActualBorelDiracZeroProjectionMap
          (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 ∧
      (∀ n : ℕ, spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0)) ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      ∀ k : ℕ,
        (0 : ℝ) ∈ (F k).1 →
          spectralMeasurePVMActualBorelDiracZeroProjectionMap
              (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
                spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) ∧
          (∀ n : ℕ, n ≠ k →
            spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0))

/-- The support-reduction target is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_support_law_target_ready,
    (by
      intro F hno
      exact spectral_measure_pvm_actual_borel_dirac_zero_no_hit_union_and_family_zero F hno),
    (by
      intro F hdis k hk
      exact spectral_measure_pvm_actual_borel_dirac_zero_countable_union_eq_hit_projection_and_zero_elsewhere
        F hdis hk)⟩

/-- Bridge after the Dirac-zero support reduction. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableSupportPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The bridge after the Dirac-zero support reduction is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_support_public_boundary_held,
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
