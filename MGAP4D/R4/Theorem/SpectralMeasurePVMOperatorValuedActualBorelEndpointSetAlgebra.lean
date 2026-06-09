import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelEndpointCarrier

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Complement laws for the actual Borel endpoint carrier in `Set ℝ`. -/
def SpectralMeasurePVMActualBorelEndpointComplementTarget : Prop :=
  (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet)ᶜ =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∧
  (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet)ᶜ =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet

/-- Complement laws for the actual Borel endpoint carrier are ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_complement_target_ready :
    SpectralMeasurePVMActualBorelEndpointComplementTarget := by
  constructor <;> simp [spectralMeasurePVMActualBorelEndpointCarrierFromSlot]

/-- Union laws for the actual Borel endpoint carrier in `Set ℝ`. -/
def SpectralMeasurePVMActualBorelEndpointUnionTarget : Prop :=
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∪
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∪
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∪
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∪
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet

/-- Union laws for the actual Borel endpoint carrier are ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_union_target_ready :
    SpectralMeasurePVMActualBorelEndpointUnionTarget := by
  repeat constructor <;> simp [spectralMeasurePVMActualBorelEndpointCarrierFromSlot]

/-- Intersection laws for the actual Borel endpoint carrier in `Set ℝ`. -/
def SpectralMeasurePVMActualBorelEndpointInterTarget : Prop :=
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∩
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∩
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∩
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∩
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet

/-- Intersection laws for the actual Borel endpoint carrier are ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_inter_target_ready :
    SpectralMeasurePVMActualBorelEndpointInterTarget := by
  repeat constructor <;> simp [spectralMeasurePVMActualBorelEndpointCarrierFromSlot]

/-- Measurability closure for the endpoint complement/union/intersection surface. -/
def SpectralMeasurePVMActualBorelEndpointBooleanMeasurabilityTarget : Prop :=
  MeasurableSet ((spectralMeasurePVMActualBorelEndpointCarrierFromSlot
    SpectralMeasurePVMSpectralSetSlot.emptySet)ᶜ) ∧
  MeasurableSet ((spectralMeasurePVMActualBorelEndpointCarrierFromSlot
    SpectralMeasurePVMSpectralSetSlot.wholeSet)ᶜ) ∧
  MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∪
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet) ∧
  MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∪
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet) ∧
  MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∩
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet) ∧
  MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet ∩
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet)

/-- Endpoint Boolean measurability closure is ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_boolean_measurability_target_ready :
    SpectralMeasurePVMActualBorelEndpointBooleanMeasurabilityTarget := by
  repeat constructor <;> simp [spectralMeasurePVMActualBorelEndpointCarrierFromSlot]

/-- Actual Borel endpoint set-algebra target. -/
def SpectralMeasurePVMActualBorelEndpointSetAlgebraTarget : Prop :=
  SpectralMeasurePVMActualBorelEndpointCarrierRealizationTarget ∧
  SpectralMeasurePVMActualBorelEndpointMeasurabilityTarget ∧
  SpectralMeasurePVMActualBorelEndpointComplementTarget ∧
  SpectralMeasurePVMActualBorelEndpointUnionTarget ∧
  SpectralMeasurePVMActualBorelEndpointInterTarget ∧
  SpectralMeasurePVMActualBorelEndpointBooleanMeasurabilityTarget

/-- The actual Borel endpoint set-algebra target is ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_set_algebra_target_ready :
    SpectralMeasurePVMActualBorelEndpointSetAlgebraTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_carrier_realization_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_measurability_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_complement_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_union_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_inter_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_boolean_measurability_target_ready⟩

/-- Actual Borel endpoint set-algebra bridge.

This local bridge advances from endpoint carrier realization to endpoint Boolean
set algebra inside `Set ℝ`.  The historical `StillOpen` markers below are kept
as append-only boundary witnesses for this older local endpoint stage: at the
moment this file was introduced, arbitrary Borel realization and genuine
operator-topology countable additivity had not yet been promoted here.

They should not be read as the current global R4 status on `main`.  The current
public route is the later R4 concrete operator-topology terminal chain, in
particular `SpectralMeasurePVMOperatorTopologyR4ConcreteRouteTopLevelFinalPacketReady`,
which exposes the concrete-route final index, operator-topology convergence, and
genuine operator-topology countable-additivity bridge while preserving the
no-shell-to-full-collapse boundary. -/
def SpectralMeasurePVMActualBorelEndpointSetAlgebraBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelEndpointCarrierPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelEndpointSetAlgebraTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual Borel endpoint set-algebra bridge is ready as a historical local
endpoint-stage boundary object.  For the current global R4 status, use the
operator-topology R4 concrete route top-level final packet and the R1--R7
terminal discharge chain. -/
theorem spectral_measure_pvm_actual_borel_endpoint_set_algebra_bridge_ready :
    SpectralMeasurePVMActualBorelEndpointSetAlgebraBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_carrier_public_boundary_held,
    spectral_measure_pvm_actual_borel_endpoint_set_algebra_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual Borel endpoint set-algebra bridge.

This public-boundary object is retained for lineage only.  It records the local
endpoint-stage non-collapse boundary and historical deferred markers.  It is
superseded, for current public routing, by the later R4 operator-topology final
packet and the R1--R7 terminal discharge chain. -/
def SpectralMeasurePVMActualBorelEndpointSetAlgebraPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelEndpointSetAlgebraBridgeReady ∧
  SpectralMeasurePVMActualBorelEndpointSetAlgebraTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual Borel endpoint set-algebra bridge is
held as a historical local endpoint-stage boundary object. -/
theorem spectral_measure_pvm_actual_borel_endpoint_set_algebra_public_boundary_held :
    SpectralMeasurePVMActualBorelEndpointSetAlgebraPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_set_algebra_bridge_ready,
    spectral_measure_pvm_actual_borel_endpoint_set_algebra_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
