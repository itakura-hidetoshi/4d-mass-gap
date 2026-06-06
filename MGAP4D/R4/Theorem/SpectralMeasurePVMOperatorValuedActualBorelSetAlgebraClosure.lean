import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSetWrapper

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Closure target for the actual Borel carrier wrapper.

The statements are phrased extensionally through the forgetful projection to
`Set ℝ`.  This keeps the proof robust: proof witnesses of measurability remain
irrelevant, while the carrier is genuinely the subtype of measurable subsets. -/
def SpectralMeasurePVMActualBorelSetAlgebraClosureTarget : Prop :=
  (∀ s : SpectralMeasurePVMActualBorelCarrierSet,
      ∃ u : SpectralMeasurePVMActualBorelCarrierSet, u.1 = s.1ᶜ) ∧
  (∀ s t : SpectralMeasurePVMActualBorelCarrierSet,
      ∃ u : SpectralMeasurePVMActualBorelCarrierSet, u.1 = s.1 ∪ t.1) ∧
  (∀ s t : SpectralMeasurePVMActualBorelCarrierSet,
      ∃ u : SpectralMeasurePVMActualBorelCarrierSet, u.1 = s.1 ∩ t.1)

/-- The actual Borel carrier wrapper is closed under complement, union, and
intersection. -/
theorem spectral_measure_pvm_actual_borel_set_algebra_closure_target_ready :
    SpectralMeasurePVMActualBorelSetAlgebraClosureTarget := by
  exact ⟨
    (by
      intro s
      exact ⟨spectralMeasurePVMActualBorelCarrierSetCompl s, rfl⟩),
    (by
      intro s t
      exact ⟨spectralMeasurePVMActualBorelCarrierSetUnion s t, rfl⟩),
    (by
      intro s t
      exact ⟨spectralMeasurePVMActualBorelCarrierSetInter s t, rfl⟩)⟩

/-- Endpoint Boolean closure laws in the actual Borel carrier wrapper, stated
after forgetting back to `Set ℝ`. -/
def SpectralMeasurePVMActualBorelSetAlgebraEndpointClosureTarget : Prop :=
  (spectralMeasurePVMActualBorelCarrierSetCompl
      spectralMeasurePVMActualBorelEmptySet).1 = (Set.univ : Set ℝ) ∧
  (spectralMeasurePVMActualBorelCarrierSetCompl
      spectralMeasurePVMActualBorelUnivSet).1 = (∅ : Set ℝ) ∧
  (spectralMeasurePVMActualBorelCarrierSetUnion
      spectralMeasurePVMActualBorelEmptySet
      spectralMeasurePVMActualBorelUnivSet).1 = (Set.univ : Set ℝ) ∧
  (spectralMeasurePVMActualBorelCarrierSetUnion
      spectralMeasurePVMActualBorelUnivSet
      spectralMeasurePVMActualBorelEmptySet).1 = (Set.univ : Set ℝ) ∧
  (spectralMeasurePVMActualBorelCarrierSetInter
      spectralMeasurePVMActualBorelEmptySet
      spectralMeasurePVMActualBorelUnivSet).1 = (∅ : Set ℝ) ∧
  (spectralMeasurePVMActualBorelCarrierSetInter
      spectralMeasurePVMActualBorelUnivSet
      spectralMeasurePVMActualBorelEmptySet).1 = (∅ : Set ℝ)

/-- Endpoint Boolean closure laws in the actual Borel carrier wrapper are ready. -/
theorem spectral_measure_pvm_actual_borel_set_algebra_endpoint_closure_target_ready :
    SpectralMeasurePVMActualBorelSetAlgebraEndpointClosureTarget := by
  repeat constructor <;>
    simp [spectralMeasurePVMActualBorelCarrierSetCompl,
      spectralMeasurePVMActualBorelCarrierSetUnion,
      spectralMeasurePVMActualBorelCarrierSetInter,
      spectralMeasurePVMActualBorelEmptySet,
      spectralMeasurePVMActualBorelUnivSet]

/-- Actual Borel set-algebra closure bridge.

This step strengthens the previous wrapper surface: arbitrary measurable subsets
of `ℝ` are now equipped with explicit complement/union/intersection closure
witnesses.  This still does not promote the wrapper into a genuine
operator-valued spectral measure; countable additivity and the spectral theorem
remain open. -/
def SpectralMeasurePVMActualBorelSetAlgebraClosureBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelSetWrapperPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetAlgebraClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraEndpointClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual Borel set-algebra closure bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_set_algebra_closure_bridge_ready :
    SpectralMeasurePVMActualBorelSetAlgebraClosureBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_wrapper_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_algebra_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_endpoint_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual Borel set-algebra closure bridge. -/
def SpectralMeasurePVMActualBorelSetAlgebraClosurePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelSetAlgebraClosureBridgeReady ∧
  SpectralMeasurePVMActualBorelSetAlgebraClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraEndpointClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual Borel set-algebra closure bridge is held. -/
theorem spectral_measure_pvm_actual_borel_set_algebra_closure_public_boundary_held :
    SpectralMeasurePVMActualBorelSetAlgebraClosurePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_algebra_closure_bridge_ready,
    spectral_measure_pvm_actual_borel_set_algebra_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_endpoint_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
