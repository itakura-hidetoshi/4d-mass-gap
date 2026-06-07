import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyCountableAdditivityConditionalDischarge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Conditional bridge that replaces the previous undifferentiated
`StillOpen` marker by an explicit witness-dependent discharge surface.

A witness for actual operator-topology realization and limit-slot compatibility,
together with the existing symbolic operator-topology bridge and countable
additivity discharge target, is enough to state the conditional genuine
operator-topology countable-additivity bridge. -/
def SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness) : Prop :=
  SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady ∧
  SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalDischargeCriterion w ∧
  w.actualOperatorTopologyRealization ∧
  w.limitSlotRealizationCompatibility ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTargetReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The conditional operator-topology countable-additivity bridge is ready from
an explicit realization witness. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_bridge_ready
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness) :
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w := by
  exact ⟨
    spectral_measure_pvm_operator_valued_genuine_operator_topology_countable_additivity_bridge_ready,
    spectral_measure_pvm_operator_topology_countable_additivity_conditional_discharge_criterion_ready w,
    w.actualOperatorTopologyRealizationReady,
    w.limitSlotRealizationCompatibilityReady,
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_operator_valued_countable_additivity_discharge_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The bridge exposes the countable-additivity equation target, not just the
symbolic limit-slot surface. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_bridge_extracts_countable_additivity_target
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness)
    (h : SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w) :
    SpectralMeasurePVMConcreteCountableAdditivityTarget := by
  rcases h with ⟨_, _, _, _, hcountable, _, _, _⟩
  exact hcountable

/-- The bridge exposes the operator-topology convergence target under the same
witness, giving the next concrete target for the analytic R4 route. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_bridge_extracts_operator_topology_convergence_target
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness)
    (h : SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w) :
    SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget := by
  rcases h with ⟨_, _, _, _, _, hconv, _, _⟩
  exact hconv

/-- The conditional bridge preserves the no-shell-collapse boundary while
removing the ambiguity about which analytic witness is missing. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_bridge_preserves_no_shell_collapse
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness)
    (h : SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
