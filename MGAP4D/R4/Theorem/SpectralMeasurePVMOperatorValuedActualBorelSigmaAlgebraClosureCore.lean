import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableUnionClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Countable intersection operation on the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetIInter
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨⋂ n, (F n).1, by
    exact MeasurableSet.iInter (fun n => (F n).2)⟩

/-- Countable intersection on the wrapper forgets to countable intersection on
`Set ℝ`. -/
theorem spectral_measure_pvm_actual_borel_carrier_set_iInter_forget
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    (spectralMeasurePVMActualBorelCarrierSetIInter F).1 = ⋂ n, (F n).1 := by
  rfl

/-- Closure target for countable intersections of actual Borel carrier sets. -/
def SpectralMeasurePVMActualBorelCountableInterClosureTarget : Prop :=
  ∀ F : ℕ → SpectralMeasurePVMActualBorelCarrierSet,
    ∃ u : SpectralMeasurePVMActualBorelCarrierSet, u.1 = ⋂ n, (F n).1

/-- The actual Borel carrier wrapper is closed under countable intersections. -/
theorem spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready :
    SpectralMeasurePVMActualBorelCountableInterClosureTarget := by
  intro F
  exact ⟨spectralMeasurePVMActualBorelCarrierSetIInter F, rfl⟩

/-- Endpoint sanity target for countable intersections: the constant-universe
family has universe intersection after forgetting to `Set ℝ`. -/
def SpectralMeasurePVMActualBorelCountableInterEndpointTarget : Prop :=
  (spectralMeasurePVMActualBorelCarrierSetIInter
      (fun _ : ℕ => spectralMeasurePVMActualBorelUnivSet)).1 = (Set.univ : Set ℝ)

/-- Endpoint sanity for the constant-universe countable intersection. -/
theorem spectral_measure_pvm_actual_borel_countable_inter_endpoint_target_ready :
    SpectralMeasurePVMActualBorelCountableInterEndpointTarget := by
  dsimp [SpectralMeasurePVMActualBorelCountableInterEndpointTarget,
    spectralMeasurePVMActualBorelCarrierSetIInter,
    spectralMeasurePVMActualBorelUnivSet]
  ext x
  simp

/-- Sigma-algebra closure core for the actual Borel carrier wrapper.

This is stronger than the earlier finite Boolean closure: it records complement,
finite union/intersection, countable union, and countable intersection closure on
the actual subtype `{s : Set ℝ // MeasurableSet s}`.  It still does not assert
operator-topology countable additivity or the self-adjoint spectral theorem. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady : Prop :=
  SpectralMeasurePVMActualBorelSetAlgebraClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableUnionClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableInterClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableUnionEndpointTarget ∧
  SpectralMeasurePVMActualBorelCountableInterEndpointTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The sigma-algebra closure core for the actual Borel carrier wrapper is ready. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_ready :
    SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_algebra_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_union_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_union_endpoint_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_endpoint_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel sigma-algebra closure core. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady ∧
  SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableInterClosureTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel sigma-algebra closure core is held. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_public_boundary_held :
    SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_ready,
    spectral_measure_pvm_actual_borel_countable_union_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
