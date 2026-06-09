import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroPVMLawsTheorem
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelGenuineSpectralMeasureConstructionReceiver

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete genuine PVM construction for the Dirac-zero actual-Borel route.

The carrier is the actual-Borel carrier already used by the R4 chain, and the
operator assignment is the Dirac-zero projection kernel.  The package carries
endpoint laws, projection laws, intersection multiplicativity, disjoint finite
additivity, and countable additivity in the installed operator-topology route. -/
structure SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction where
  kernel : SpectralMeasurePVMActualBorelProjectionKernel
  kernel_is_dirac_zero : kernel = spectralMeasurePVMActualBorelDiracZeroProjectionKernel
  pvm_laws : SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem
  pvm_laws_public_boundary : SpectralMeasurePVMActualBorelDiracZeroPVMLawsPublicBoundaryHeld
  construction_receiver_ready :
    SpectralMeasurePVMActualBorelGenuineSpectralMeasureConstructionReceiverBridgeReady
  receiver_public_boundary :
    SpectralMeasurePVMActualBorelGenuineSpectralMeasureConstructionReceiverPublicBoundaryHeld
  no_shell_collapse : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The constructed Dirac-zero object is a genuine actual-Borel PVM package. -/
def SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstructionTheorem : Prop :=
  Nonempty SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelGenuineSpectralMeasureConstructionReceiverBridgeReady ∧
  SpectralMeasurePVMActualBorelGenuineSpectralMeasureConstructionReceiverPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Canonical Dirac-zero actual-Borel genuine PVM construction. -/
def spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction :
    SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction where
  kernel := spectralMeasurePVMActualBorelDiracZeroProjectionKernel
  kernel_is_dirac_zero := rfl
  pvm_laws := spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem
  pvm_laws_public_boundary :=
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_public_boundary_held
  construction_receiver_ready :=
    spectral_measure_pvm_actual_borel_genuine_spectral_measure_construction_receiver_bridge_ready
  receiver_public_boundary :=
    spectral_measure_pvm_actual_borel_genuine_spectral_measure_construction_receiver_public_boundary_held
  no_shell_collapse := spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- The Dirac-zero actual-Borel genuine PVM construction theorem. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_genuine_pvm_construction_theorem :
    SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstructionTheorem := by
  exact ⟨
    ⟨spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction⟩,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.pvm_laws,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.pvm_laws_public_boundary,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.construction_receiver_ready,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.receiver_public_boundary,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.no_shell_collapse⟩

/-- Projection: endpoint and PVM laws of the constructed Dirac-zero object. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_genuine_pvm_laws :
    SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem := by
  exact spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.pvm_laws

/-- Projection: the construction remains attached to the genuine spectral-measure
receiver boundary. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_genuine_pvm_receiver_bridge_ready :
    SpectralMeasurePVMActualBorelGenuineSpectralMeasureConstructionReceiverBridgeReady := by
  exact spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.construction_receiver_ready

/-- Public boundary for the Dirac-zero genuine PVM construction theorem. -/
def SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstructionPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMActualBorelGenuineSpectralMeasureConstructionReceiverPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the Dirac-zero genuine PVM construction is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_genuine_pvm_construction_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroGenuinePVMConstructionPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_genuine_pvm_construction_theorem,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.pvm_laws,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.receiver_public_boundary,
    spectralMeasurePVMActualBorelDiracZeroGenuinePVMConstruction.no_shell_collapse⟩

end

end Theorem
end R4
end MGAP4D
