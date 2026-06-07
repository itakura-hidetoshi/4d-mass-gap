import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridge
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTarget

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- External witness package for the first genuinely missing analytic step in R4:
turning the symbolic zero/identity limit slots into an actual operator-topology
realization, and proving compatibility between those slots and the intended
operator-topology limits.

This is deliberately not a receipt.  It records the two pieces of data that are
missing from the current bridge before the symbolic countable-additivity surface
can be treated as a genuine operator-topology countable-additivity step. -/
structure SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness where
  actualOperatorTopologyRealization : Prop
  limitSlotRealizationCompatibility : Prop
  actualOperatorTopologyRealizationReady : actualOperatorTopologyRealization
  limitSlotRealizationCompatibilityReady : limitSlotRealizationCompatibility

/-- Conditional discharge criterion for operator-topology countable additivity.

Given a genuine realization witness, the existing R4 symbolic interface,
zero/identity branch law, finite-partial slot law, and countable-additivity
discharge target are enough to form the next analytic discharge criterion.  This
shrinks the open frontier to the two witness fields above, rather than adding
another shell receipt. -/
def SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalDischargeCriterion
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness) : Prop :=
  SpectralMeasurePVMOperatorTopologyCountableAdditivityInterfaceExistenceTarget ∧
  SpectralMeasurePVMSymbolicOperatorTopologyCountableAdditivityBranchTarget ∧
  SpectralMeasurePVMOperatorTopologyLimitSlotBranchTarget ∧
  SpectralMeasurePVMOperatorTopologyFinitePartialSlotTarget ∧
  w.actualOperatorTopologyRealization ∧
  w.limitSlotRealizationCompatibility ∧
  SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTargetReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The conditional operator-topology countable-additivity discharge criterion is
available as soon as a genuine realization witness is supplied. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_discharge_criterion_ready
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness) :
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalDischargeCriterion w := by
  exact ⟨
    spectral_measure_pvm_operator_topology_countable_additivity_interface_existence_target_ready,
    spectral_measure_pvm_symbolic_operator_topology_countable_additivity_branch_target_ready,
    spectral_measure_pvm_operator_topology_limit_slot_branch_target_ready,
    spectral_measure_pvm_operator_topology_finite_partial_slot_target_ready,
    w.actualOperatorTopologyRealizationReady,
    w.limitSlotRealizationCompatibilityReady,
    spectral_measure_pvm_operator_valued_countable_additivity_discharge_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The criterion projects out the exact remaining actual realization field. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_discharge_extracts_actual_realization
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness)
    (h : SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalDischargeCriterion w) :
    w.actualOperatorTopologyRealization := by
  rcases h with ⟨_, _, _, _, hactual, _⟩
  exact hactual

/-- The criterion projects out the exact remaining slot-compatibility field. -/
theorem spectral_measure_pvm_operator_topology_countable_additivity_conditional_discharge_extracts_limit_slot_compatibility
    (w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness)
    (h : SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalDischargeCriterion w) :
    w.limitSlotRealizationCompatibility := by
  rcases h with ⟨_, _, _, _, _, hcompat, _⟩
  exact hcompat

end

end Theorem
end R4
end MGAP4D
