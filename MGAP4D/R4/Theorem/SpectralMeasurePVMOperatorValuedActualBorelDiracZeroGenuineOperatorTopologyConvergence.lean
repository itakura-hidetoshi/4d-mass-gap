import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroConcreteTsum

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Genuine operator-topology convergence theorem for the Dirac-zero actual-Borel
route.

This is no longer a target/receipt: for every pairwise-disjoint actual-Borel
countable family, the concrete `tsum` of the Dirac-zero summand projections is
identically the Dirac-zero projection of the countable union. -/
def SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem : Prop :=
  ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
          (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) =
        spectralMeasurePVMActualBorelDiracZeroUnionProjection F

/-- The Dirac-zero actual-Borel operator-topology convergence theorem is proved
by the concrete `tsum` countable-additivity theorem. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_theorem :
    SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem := by
  intro F hdis
  exact spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_realizes_countable_additivity
    F hdis

/-- The Dirac-zero route upgrades the former operator-topology convergence target
into a genuine theorem.

The old symbolic target can still exist for legacy/general R4 routes, but this
Dirac-zero actual-Borel route no longer stops at that target: it carries a
concrete `tsum` theorem. -/
def SpectralMeasurePVMActualBorelDiracZeroOperatorTopologyConvergencePromotedFromTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityClosed ∧
  SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero operator-topology convergence target is promoted to a genuine
theorem. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_operator_topology_convergence_promoted_from_target :
    SpectralMeasurePVMActualBorelDiracZeroOperatorTopologyConvergencePromotedFromTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_countable_additivity_closed,
    spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_countable_additivity_public_boundary_held,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after promoting Dirac-zero operator-topology convergence from
target to theorem. -/
def SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergencePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroOperatorTopologyConvergencePromotedFromTarget ∧
  SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after promoting Dirac-zero operator-topology convergence
from target to theorem is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergencePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_operator_topology_convergence_promoted_from_target,
    spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_theorem,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
