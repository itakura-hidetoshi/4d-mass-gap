import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableDisjointnessFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Addition table for symbolic spectral-integral slots.  The `identity + identity`
branch is totalized as `zeroIntegral`, mirroring the concrete operator-addition
table.  It is not used by disjoint finite additivity, since `(whole, whole)` is
not disjoint. -/
def spectralMeasurePVMSpectralIntegralSlotAdd :
    SpectralMeasurePVMSpectralIntegralSlot →
      SpectralMeasurePVMSpectralIntegralSlot →
        SpectralMeasurePVMSpectralIntegralSlot
  | SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral, a => a
  | SpectralMeasurePVMSpectralIntegralSlot.identityIntegral,
      SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral =>
      SpectralMeasurePVMSpectralIntegralSlot.identityIntegral
  | SpectralMeasurePVMSpectralIntegralSlot.identityIntegral,
      SpectralMeasurePVMSpectralIntegralSlot.identityIntegral =>
      SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral

/-- Operator finite additivity on disjoint supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_operator_finite_additivity
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hdisj : SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) := by
  cases E <;> cases F <;> try rfl
  cases hdisj

/-- Reversed operator finite additivity on disjoint supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_operator_finite_additivity_reversed
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hdisj : SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) := by
  cases E <;> cases F <;> try rfl
  cases hdisj

/-- Symbolic spectral-integral finite additivity on disjoint supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_spectral_integral_finite_additivity
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hdisj : SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F) :
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMSpectralIntegralSlotAdd
        (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E)
        (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F) := by
  cases E <;> cases F <;> try rfl
  cases hdisj

/-- Reversed symbolic spectral-integral finite additivity on disjoint supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_spectral_integral_finite_additivity_reversed
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hdisj : SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F) :
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMSpectralIntegralSlotAdd
        (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F)
        (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E) := by
  cases E <;> cases F <;> try rfl
  cases hdisj

/-- Operator finite-additivity equality reflects disjointness on the supported
local surface. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_finite_additivity_reflects_disjoint
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hadd : spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F := by
  cases E <;> cases F
  · rfl
  · rfl
  · rfl
  · have hbad :
        SpectralMeasurePVMConcreteBoundedOperator.identity =
          SpectralMeasurePVMConcreteBoundedOperator.zero := by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetUnion,
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate,
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot,
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate,
        spectralMeasurePVMConcreteNormalizationCandidate,
        spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
        spectralMeasurePVMConcreteOperatorAdd] using hadd
    cases hbad

/-- Symbolic spectral-integral finite-additivity equality reflects disjointness on
the supported local surface. -/
theorem spectral_measure_pvm_finite_supported_measurable_spectral_integral_finite_additivity_reflects_disjoint
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hadd : spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMSpectralIntegralSlotAdd
        (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E)
        (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F)) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F := by
  cases E <;> cases F
  · rfl
  · rfl
  · rfl
  · have hbad :
        SpectralMeasurePVMSpectralIntegralSlot.identityIntegral =
          SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral := by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetUnion,
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot,
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate,
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot,
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate,
        spectralMeasurePVMConcreteNormalizationCandidate,
        spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
        spectralMeasurePVMSpectralIntegralSlotFromOperator,
        spectralMeasurePVMSpectralIntegralSlotAdd] using hadd
    cases hbad

/-- Disjointness is equivalent to operator finite additivity on the supported
local surface. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_iff_operator_finite_additivity
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) := by
  constructor
  · exact spectral_measure_pvm_finite_supported_measurable_disjoint_operator_finite_additivity E F
  · exact spectral_measure_pvm_finite_supported_measurable_operator_finite_additivity_reflects_disjoint E F

/-- Disjointness is equivalent to symbolic spectral-integral finite additivity on
the supported local surface. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_iff_spectral_integral_finite_additivity
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMSpectralIntegralSlotAdd
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E)
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F) := by
  constructor
  · exact spectral_measure_pvm_finite_supported_measurable_disjoint_spectral_integral_finite_additivity E F
  · exact spectral_measure_pvm_finite_supported_measurable_spectral_integral_finite_additivity_reflects_disjoint E F

/-- Finite-additivity reading target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableFiniteAdditivityReadingTarget : Prop :=
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F →
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F →
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F →
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMSpectralIntegralSlotAdd
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E)
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F →
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMSpectralIntegralSlotAdd
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F)
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMSpectralIntegralSlotAdd
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E)
          (spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F))

/-- The supported measurable finite-additivity reading target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_finite_additivity_reading_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableFiniteAdditivityReadingTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_disjoint_operator_finite_additivity,
    spectral_measure_pvm_finite_supported_measurable_disjoint_operator_finite_additivity_reversed,
    spectral_measure_pvm_finite_supported_measurable_disjoint_spectral_integral_finite_additivity,
    spectral_measure_pvm_finite_supported_measurable_disjoint_spectral_integral_finite_additivity_reversed,
    spectral_measure_pvm_finite_supported_measurable_disjoint_iff_operator_finite_additivity,
    spectral_measure_pvm_finite_supported_measurable_disjoint_iff_spectral_integral_finite_additivity⟩

/-- Bridge registering finite-additivity reading for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableFiniteAdditivityReadingBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableLocalOrthogonalityReadingCertificateReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableFiniteAdditivityReadingTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableDisjointnessPublicBoundaryHeld ∧
  SpectralMeasurePVMFiniteSetCarrierImageFiniteAdditivityTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCoreReady ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable finite-additivity reading bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_finite_additivity_reading_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableFiniteAdditivityReadingBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_orthogonality_reading_certificate_ready,
    spectral_measure_pvm_finite_supported_measurable_finite_additivity_reading_target_ready,
    spectral_measure_pvm_finite_supported_measurable_disjointness_public_boundary_held,
    spectral_measure_pvm_finite_set_carrier_image_finite_additivity_target_ready,
    spectral_measure_pvm_operator_valued_concrete_finite_additivity_core_ready,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
