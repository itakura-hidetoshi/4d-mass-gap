import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteMeasurableLocalPVMFinalReceiptBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Supported measurable sets for the finite R4 local carrier.

This restricts the local measurable carrier to the two sets actually used by the
R4 local PVM surface: `∅` and `univ`.  It is a concrete local measurable set
class, not the full Borel sigma algebra. -/
inductive SpectralMeasurePVMFiniteSupportedMeasurableSet where
  | empty
  | whole
  deriving DecidableEq

/-- Realize a supported measurable set as an actual set in the finite carrier. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetToSet :
    SpectralMeasurePVMFiniteSupportedMeasurableSet → SpectralMeasurePVMFiniteSetCarrier
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.empty => spectralMeasurePVMFiniteSetCarrierEmpty
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.whole => spectralMeasurePVMFiniteSetCarrierWhole

/-- Realize a supported measurable set as the corresponding spectral slot. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetToSlot :
    SpectralMeasurePVMFiniteSupportedMeasurableSet → SpectralMeasurePVMSpectralSetSlot
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.empty => SpectralMeasurePVMSpectralSetSlot.emptySet
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.whole => SpectralMeasurePVMSpectralSetSlot.wholeSet

/-- Operator assignment on supported measurable sets. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMConcreteBoundedOperator :=
  spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
    (spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E)

/-- Complement on supported measurable sets. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetComplement :
    SpectralMeasurePVMFiniteSupportedMeasurableSet →
      SpectralMeasurePVMFiniteSupportedMeasurableSet
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.empty =>
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.whole =>
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- Union on supported measurable sets. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetUnion :
    SpectralMeasurePVMFiniteSupportedMeasurableSet →
      SpectralMeasurePVMFiniteSupportedMeasurableSet →
        SpectralMeasurePVMFiniteSupportedMeasurableSet
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.empty,
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty =>
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty
  | _, _ => SpectralMeasurePVMFiniteSupportedMeasurableSet.whole

/-- Intersection on supported measurable sets. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetInter :
    SpectralMeasurePVMFiniteSupportedMeasurableSet →
      SpectralMeasurePVMFiniteSupportedMeasurableSet →
        SpectralMeasurePVMFiniteSupportedMeasurableSet
  | SpectralMeasurePVMFiniteSupportedMeasurableSet.whole,
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole =>
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole
  | _, _ => SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- Disjointness on supported measurable sets, transported from the concrete local relation. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetDisjoint
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) : Prop :=
  SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint
    (spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E)
    (spectralMeasurePVMFiniteSupportedMeasurableSetToSlot F)

/-- Every supported measurable set is measurable in the finite carrier. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_measurable
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E) := by
  cases E
  · exact spectral_measure_pvm_finite_set_carrier_empty_measurable
  · exact spectral_measure_pvm_finite_set_carrier_whole_measurable

/-- Endpoint operator values on supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetEndpointOperatorTarget : Prop :=
  spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty =
    SpectralMeasurePVMConcreteBoundedOperator.zero ∧
  spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole =
    SpectralMeasurePVMConcreteBoundedOperator.identity

/-- Supported measurable sets are projection-valued. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetProjectionTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMConcreteOperatorIdempotent
      (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMConcreteOperatorSelfFixed
      (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E))

/-- Supported measurable disjointness gives zero products. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetOrthogonalityTarget : Prop :=
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetDisjoint E F →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetDisjoint E F →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
        SpectralMeasurePVMConcreteBoundedOperator.zero)

/-- Binary finite additivity on supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetFiniteAdditivityTarget : Prop :=
  ∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetDisjoint E F →
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)

/-- Endpoint operator target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_endpoint_operator_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetEndpointOperatorTarget := by
  exact ⟨rfl, rfl⟩

/-- Projection-valued target is ready on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_projection_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetProjectionTarget := by
  exact ⟨
    fun E => by cases E <;> rfl,
    fun E => by cases E <;> rfl⟩

/-- Orthogonality target is ready on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_orthogonality_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetOrthogonalityTarget := by
  exact ⟨
    fun E F hEF => by
      cases E <;> cases F <;> try rfl
      exact False.elim hEF,
    fun E F hEF => by
      cases E <;> cases F <;> try rfl
      exact False.elim hEF⟩

/-- Finite additivity target is ready on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_finite_additivity_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetFiniteAdditivityTarget := by
  intro E F hEF
  cases E <;> cases F <;> try rfl
  exact False.elim hEF

/-- Bundle for the finite supported measurable-set local PVM surface. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetBridgeReady : Prop :=
  SpectralMeasurePVMFiniteMeasurableLocalPVMFinalReceiptBridgeReady ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)) ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetEndpointOperatorTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetProjectionTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetOrthogonalityTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetFiniteAdditivityTarget ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite supported measurable-set local PVM bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_measurable_local_pvm_final_receipt_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_set_measurable,
    spectral_measure_pvm_finite_supported_measurable_set_endpoint_operator_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_projection_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_orthogonality_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_finite_additivity_target_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
