import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableBooleanCompatibility

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Complement is involutive on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_complement_involutive
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetComplement
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) = E := by
  cases E <;> rfl

/-- Union is commutative on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_comm
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F =
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion F E := by
  cases E <;> cases F <;> rfl

/-- Intersection is commutative on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_comm
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E F =
      spectralMeasurePVMFiniteSupportedMeasurableSetInter F E := by
  cases E <;> cases F <;> rfl

/-- Union is associative on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_assoc
    (E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) G =
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion F G) := by
  cases E <;> cases F <;> cases G <;> rfl

/-- Intersection is associative on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_assoc
    (E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) G =
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter F G) := by
  cases E <;> cases F <;> cases G <;> rfl

/-- Empty is the left identity for union. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_empty_left
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion
        SpectralMeasurePVMFiniteSupportedMeasurableSet.empty E = E := by
  cases E <;> rfl

/-- Empty is the right identity for union. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_empty_right
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
        SpectralMeasurePVMFiniteSupportedMeasurableSet.empty = E := by
  cases E <;> rfl

/-- Whole is the left identity for intersection. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_whole_left
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter
        SpectralMeasurePVMFiniteSupportedMeasurableSet.whole E = E := by
  cases E <;> rfl

/-- Whole is the right identity for intersection. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_whole_right
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E
        SpectralMeasurePVMFiniteSupportedMeasurableSet.whole = E := by
  cases E <;> rfl

/-- Union is idempotent on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_idempotent
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E E = E := by
  cases E <;> rfl

/-- Intersection is idempotent on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_idempotent
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E E = E := by
  cases E <;> rfl

/-- Union absorbs intersection. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_absorb_inter
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) = E := by
  cases E <;> cases F <;> rfl

/-- Intersection absorbs union. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_absorb_union
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) = E := by
  cases E <;> cases F <;> rfl

/-- De Morgan law for complement of union. -/
theorem spectral_measure_pvm_finite_supported_measurable_complement_union
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetComplement
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetInter
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement F) := by
  cases E <;> cases F <;> rfl

/-- De Morgan law for complement of intersection. -/
theorem spectral_measure_pvm_finite_supported_measurable_complement_inter
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetComplement
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement F) := by
  cases E <;> cases F <;> rfl

/-- Boolean algebra law target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetComplement
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) = E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F =
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion F E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E F =
      spectralMeasurePVMFiniteSupportedMeasurableSetInter F E) ∧
  (∀ E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) G =
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion F G)) ∧
  (∀ E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetInter
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) G =
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter F G)) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion
        SpectralMeasurePVMFiniteSupportedMeasurableSet.empty E = E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetInter
        SpectralMeasurePVMFiniteSupportedMeasurableSet.whole E = E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E E = E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E E = E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) = E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) = E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetComplement
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetInter
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement F)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetComplement
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement F))

/-- The supported measurable Boolean algebra law target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_boolean_algebra_law_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_complement_involutive,
    spectral_measure_pvm_finite_supported_measurable_union_comm,
    spectral_measure_pvm_finite_supported_measurable_inter_comm,
    spectral_measure_pvm_finite_supported_measurable_union_assoc,
    spectral_measure_pvm_finite_supported_measurable_inter_assoc,
    spectral_measure_pvm_finite_supported_measurable_union_empty_left,
    spectral_measure_pvm_finite_supported_measurable_inter_whole_left,
    spectral_measure_pvm_finite_supported_measurable_union_idempotent,
    spectral_measure_pvm_finite_supported_measurable_inter_idempotent,
    spectral_measure_pvm_finite_supported_measurable_union_absorb_inter,
    spectral_measure_pvm_finite_supported_measurable_inter_absorb_union,
    spectral_measure_pvm_finite_supported_measurable_complement_union,
    spectral_measure_pvm_finite_supported_measurable_complement_inter⟩

/-- Bridge registering the supported measurable Boolean algebra laws. -/
def SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalFullAxiomPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable Boolean algebra law bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_boolean_algebra_law_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_boolean_compatibility_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_boolean_algebra_law_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_full_axiom_public_boundary_held,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
