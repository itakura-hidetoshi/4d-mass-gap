import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroSpectralMeasureCountableAdditivity

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual spectral-measure laws theorem for the Dirac-zero actual-Borel route.

This theorem package is phrased at the `SpectralMeasurePVMActualBorelDiracZeroSpectralMeasure`
interface, not merely at the concrete branch/evaluator level.  It records the
endpoint laws and countable additivity as fields/laws of the actual spectral
measure, then includes the previously proved PVM laws package for the same
underlying map. -/
def SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawsTheorem : Prop :=
  spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.empty_maps_to_zero ∧
  spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.univ_maps_to_identity ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual spectral-measure laws theorem for the Dirac-zero route is proved. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_actual_spectral_measure_laws_theorem :
    SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawsTheorem := by
  exact ⟨
    spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.empty_maps_to_zero,
    spectralMeasurePVMActualBorelDiracZeroSpectralMeasure.univ_maps_to_identity,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_law,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The actual spectral-measure interface is fully law-carrying for the Dirac-zero
route.  Upper layers should depend on this theorem package rather than on the
older concrete branch-only countable-additivity theorem. -/
def SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawCarryingInterfaceReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawsTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityClosed ∧
  SpectralMeasurePVMActualBorelDiracZeroSafeUseTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual spectral-measure law-carrying interface is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_actual_spectral_measure_law_carrying_interface_ready :
    SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawCarryingInterfaceReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_actual_spectral_measure_laws_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_closed,
    spectral_measure_pvm_actual_borel_dirac_zero_safe_use_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after promoting countable additivity to the actual spectral
measure law-carrying interface. -/
def SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawsPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawCarryingInterfaceReady ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureCountableAdditivityPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after promoting countable additivity to the actual
spectral-measure law-carrying interface is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_actual_spectral_measure_laws_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroActualSpectralMeasureLawsPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_actual_spectral_measure_law_carrying_interface_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_countable_additivity_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
