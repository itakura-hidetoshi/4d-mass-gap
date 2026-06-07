import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroCountableAdditivityReduction

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A countable family of actual-Borel projection operators is pointwise a zero
series. -/
def SpectralMeasurePVMActualBorelProjectionOperatorPointwiseZeroSeries
    (A : ℕ → SpectralMeasurePVMActualBorelProjectionOperator) : Prop :=
  ∀ n : ℕ, ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier, A n x = 0

/-- A countable family of actual-Borel projection operators is pointwise supported
at a single index `k`. -/
def SpectralMeasurePVMActualBorelProjectionOperatorPointwiseOneHitSeries
    (A : ℕ → SpectralMeasurePVMActualBorelProjectionOperator) (k : ℕ) : Prop :=
  ∀ n : ℕ, n ≠ k →
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier, A n x = 0

/-- If no actual-Borel family member contains the Dirac base point, the induced
operator sequence is pointwise zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_no_hit_pointwise_zero_series
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hno : ¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) :
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseZeroSeries
      (fun n => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n)) := by
  intro n x
  have hzero :=
    spectral_measure_pvm_actual_borel_dirac_zero_no_hit_all_projections_zero F hno n
  rw [hzero]
  rfl

/-- If a pairwise-disjoint family has a hit at `k`, the induced operator sequence
is pointwise one-hit supported at `k`. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_hit_pointwise_one_hit_series
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {k : ℕ}
    (hk : (0 : ℝ) ∈ (F k).1) :
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseOneHitSeries
      (fun n => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n)) k := by
  intro n hne x
  have hzero :=
    spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_zero_away_from_hit
      F hdis hk n hne
  rw [hzero]
  rfl

/-- In the no-hit case, countable additivity reduces pointwise to the zero
operator on the union and a zero operator series. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_no_hit_countable_additivity_pointwise_reduction
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hno : ¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 ∧
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseZeroSeries
      (fun n => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n)) := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_zero_of_no_hit F hno,
    spectral_measure_pvm_actual_borel_dirac_zero_no_hit_pointwise_zero_series F hno⟩

/-- In the hit case, countable additivity reduces pointwise to a one-hit series. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_hit_countable_additivity_pointwise_reduction
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {k : ℕ}
    (hk : (0 : ℝ) ∈ (F k).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
          spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) ∧
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseOneHitSeries
      (fun n => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n)) k := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_eq_hit_projection
      F hdis hk,
    spectral_measure_pvm_actual_borel_dirac_zero_hit_pointwise_one_hit_series
      F hdis hk⟩

/-- One-hit series reduction target for Dirac-zero countable additivity. -/
def SpectralMeasurePVMActualBorelDiracZeroOneHitSeriesReductionTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionTarget ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    (¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) →
      spectralMeasurePVMActualBorelDiracZeroProjectionMap
          (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 ∧
      SpectralMeasurePVMActualBorelProjectionOperatorPointwiseZeroSeries
        (fun n => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n))) ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      ∀ k : ℕ,
        (0 : ℝ) ∈ (F k).1 →
          spectralMeasurePVMActualBorelDiracZeroProjectionMap
              (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
                spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) ∧
          SpectralMeasurePVMActualBorelProjectionOperatorPointwiseOneHitSeries
            (fun n => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n)) k)

/-- The one-hit series reduction target is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_one_hit_series_reduction_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroOneHitSeriesReductionTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_target_ready,
    (by
      intro F hno
      exact spectral_measure_pvm_actual_borel_dirac_zero_no_hit_countable_additivity_pointwise_reduction
        F hno),
    (by
      intro F hdis k hk
      exact spectral_measure_pvm_actual_borel_dirac_zero_hit_countable_additivity_pointwise_reduction
        F hdis hk)⟩

/-- Bridge after the Dirac-zero one-hit series reduction. -/
def SpectralMeasurePVMActualBorelDiracZeroOneHitSeriesReductionBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivitySupportReductionBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroOneHitSeriesReductionTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The bridge after the Dirac-zero one-hit series reduction is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_one_hit_series_reduction_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroOneHitSeriesReductionBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_support_reduction_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_one_hit_series_reduction_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
