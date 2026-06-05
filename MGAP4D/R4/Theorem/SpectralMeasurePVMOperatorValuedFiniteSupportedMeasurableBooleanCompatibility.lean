import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableLocalFullAxiomFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Complement of supported measurable sets is realized as set complement on the
finite measurable carrier. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_complement_realizes
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) =
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)ᶜ := by
  cases E <;> ext x <;>
    simp [spectralMeasurePVMFiniteSupportedMeasurableSetComplement,
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
      spectralMeasurePVMFiniteSetCarrierEmpty,
      spectralMeasurePVMFiniteSetCarrierWhole]

/-- Union of supported measurable sets is realized as set union on the finite
measurable carrier. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_union_realizes
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ∪
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet F := by
  cases E <;> cases F <;> ext x <;>
    simp [spectralMeasurePVMFiniteSupportedMeasurableSetUnion,
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
      spectralMeasurePVMFiniteSetCarrierEmpty,
      spectralMeasurePVMFiniteSetCarrierWhole]

/-- Intersection of supported measurable sets is realized as set intersection on
the finite measurable carrier. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_inter_realizes
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ∩
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet F := by
  cases E <;> cases F <;> ext x <;>
    simp [spectralMeasurePVMFiniteSupportedMeasurableSetInter,
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
      spectralMeasurePVMFiniteSetCarrierEmpty,
      spectralMeasurePVMFiniteSetCarrierWhole]

/-- Boolean compatibility target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) =
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)ᶜ) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ∪
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ∩
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet F)

/-- The supported measurable Boolean compatibility target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_boolean_compatibility_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_complement_realizes,
    spectral_measure_pvm_finite_supported_measurable_set_union_realizes,
    spectral_measure_pvm_finite_supported_measurable_set_inter_realizes⟩

/-- Bridge from the final-receipted local full-axiom surface to explicit Boolean
compatibility on the finite measurable carrier. -/
def SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableLocalFullAxiomFinalReceiptReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalFullAxiomPublicBoundaryHeld ∧
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidatePublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite supported measurable Boolean compatibility bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_boolean_compatibility_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_full_axiom_final_receipt_ready,
    spectral_measure_pvm_finite_supported_measurable_local_full_axiom_public_boundary_held,
    spectral_measure_pvm_finite_supported_measurable_boolean_compatibility_target_ready,
    spectral_measure_pvm_finite_supported_measurable_spectral_measure_candidate_public_boundary_held,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
