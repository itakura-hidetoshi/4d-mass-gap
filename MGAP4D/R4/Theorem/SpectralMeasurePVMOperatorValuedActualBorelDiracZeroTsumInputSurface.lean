import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroCountableAdditivityDichotomy

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Zero-series input shape for the Dirac-zero countable-additivity `tsum` step.

This avoids committing to a concrete Mathlib `HasSum` API before the operator
topology layer is selected: the family is already reduced to the case where the
union projection and every summand projection are zero. -/
def SpectralMeasurePVMActualBorelDiracZeroTsumZeroSeriesInput
    (F : SpectralMeasurePVMActualBorelCountableFamily) : Prop :=
  spectralMeasurePVMActualBorelDiracZeroProjectionMap
      (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 ∧
  (∀ n : ℕ, spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0)

/-- One-hit-series input shape for the Dirac-zero countable-additivity `tsum`
step.

The countable series has a unique possible nonzero summand at `k`: the union
projection is the `k`-th projection and all other summand projections are zero. -/
def SpectralMeasurePVMActualBorelDiracZeroTsumOneHitSeriesInput
    (F : SpectralMeasurePVMActualBorelCountableFamily) (k : ℕ) : Prop :=
  spectralMeasurePVMActualBorelDiracZeroProjectionMap
      (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
        spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) ∧
  (∀ n : ℕ, n ≠ k →
    spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0)

/-- Countable-additivity `tsum` input surface for a pairwise-disjoint Dirac-zero
actual-Borel family: the input is either a zero series or a one-hit series. -/
def SpectralMeasurePVMActualBorelDiracZeroTsumInputSurface
    (F : SpectralMeasurePVMActualBorelCountableFamily) : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroTsumZeroSeriesInput F ∨
  ∃ k : ℕ,
    (0 : ℝ) ∈ (F k).1 ∧
    SpectralMeasurePVMActualBorelDiracZeroTsumOneHitSeriesInput F k

/-- The dichotomy supplies the `tsum` input surface. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_of_dichotomy
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (h : SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomy F) :
    SpectralMeasurePVMActualBorelDiracZeroTsumInputSurface F := by
  rcases h with hzero | hone
  · left
    exact ⟨hzero.2.1, hzero.2.2⟩
  · rcases hone with ⟨k, hk, hhit⟩
    right
    exact ⟨k, hk, hhit⟩

/-- Pairwise-disjoint actual-Borel families produce the Dirac-zero `tsum` input
surface. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_tsum_input_surface
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F) :
    SpectralMeasurePVMActualBorelDiracZeroTsumInputSurface F := by
  exact spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_of_dichotomy F
    (spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy F hdis)

/-- Target collecting the `tsum` input surface for Dirac-zero countable
additivity. -/
def SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyTarget ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      SpectralMeasurePVMActualBorelDiracZeroTsumInputSurface F)

/-- The Dirac-zero `tsum` input surface target is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_target_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_tsum_input_surface⟩

/-- Bridge after extracting the Dirac-zero `tsum` input surface.

This is the handoff layer to the true analytic infinite-sum statement: all
set-theoretic and projection-kernel work has reduced the countable-additivity
problem to either a zero series or a one-hit series. -/
def SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableAdditivityDichotomyPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The bridge after extracting the Dirac-zero `tsum` input surface is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_additivity_dichotomy_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the Dirac-zero `tsum` input surface. -/
def SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfacePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfaceTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the Dirac-zero `tsum` input surface is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroTsumInputSurfacePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_tsum_input_surface_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
