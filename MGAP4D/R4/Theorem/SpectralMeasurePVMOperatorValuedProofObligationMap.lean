import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedTargetSpec

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Ordered proof obligations for actualizing the R4 shell into a genuine
operator-valued PVM target.

These obligations are requirements for a future implementation, not facts about
the current `PUnit` shell. -/
structure SpectralMeasurePVMOperatorValuedProofObligationMap where
  carrierHilbertSpaceBoundObligation : Prop
  boundedProjectionOperatorTargetObligation : Prop
  measurableSetDomainObligation : Prop
  normalizationIdentityObligation : Prop
  projectionIdempotenceObligation : Prop
  projectionSelfAdjointnessObligation : Prop
  orthogonalityForDisjointSetsObligation : Prop
  countableAdditivityTopologyObligation : Prop
  spectralResolutionObligation : Prop
  functionalCalculusBridgeObligation : Prop
  shellTransportObligation : Prop
  receiptPreservationObligation : Prop
  noShellCollapseObligation : Prop

/-- The current operator-valued proof-obligation map induced by the target spec. -/
def spectralMeasurePVMOperatorValuedProofObligationMap :
    SpectralMeasurePVMOperatorValuedProofObligationMap :=
  { carrierHilbertSpaceBoundObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.carrierHilbertSpaceBound
    boundedProjectionOperatorTargetObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.boundedProjectionOperatorTarget
    measurableSetDomainObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.measurableSetDomain
    normalizationIdentityObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.normalizationAsIdentity
    projectionIdempotenceObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.projectionIdempotence
    projectionSelfAdjointnessObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.projectionSelfAdjointness
    orthogonalityForDisjointSetsObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.projectionOrthogonalityForDisjointSets
    countableAdditivityTopologyObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.countableAdditivityInOperatorTopology
    spectralResolutionObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.spectralResolutionForSelfAdjointOperator
    functionalCalculusBridgeObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.functionalCalculusBridgeRequired
    shellTransportObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.shellCandidateTransportMap
    receiptPreservationObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.transportPreservesExistingShellReceipts
    noShellCollapseObligation :=
      spectralMeasurePVMOperatorValuedTargetSpec.noCollapseFromShellProofOnly }

/-- Readiness of the operator-valued proof-obligation map. -/
def SpectralMeasurePVMOperatorValuedProofObligationMapReady : Prop :=
  SpectralMeasurePVMOperatorValuedUpgradeTargetBoundary ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.carrierHilbertSpaceBoundObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.boundedProjectionOperatorTargetObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.measurableSetDomainObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.normalizationIdentityObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.projectionIdempotenceObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.projectionSelfAdjointnessObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.orthogonalityForDisjointSetsObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.countableAdditivityTopologyObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.spectralResolutionObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.functionalCalculusBridgeObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.shellTransportObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.receiptPreservationObligation ∧
  spectralMeasurePVMOperatorValuedProofObligationMap.noShellCollapseObligation

/-- The operator-valued proof-obligation map is ready. -/
theorem spectral_measure_pvm_operator_valued_proof_obligation_map_ready :
    SpectralMeasurePVMOperatorValuedProofObligationMapReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_upgrade_target_boundary_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Operator-valued proof-obligation handoff boundary.

This is the last R4 layer before actually replacing the current shell target by
an operator-valued PVM target. -/
def SpectralMeasurePVMOperatorValuedProofObligationHandoffBoundary : Prop :=
  SpectralMeasurePVMOperatorValuedProofObligationMapReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary ∧
  SpectralMeasurePVMFullAxiomsStillOpen

/-- The operator-valued proof-obligation handoff boundary is ready. -/
theorem spectral_measure_pvm_operator_valued_proof_obligation_handoff_boundary_ready :
    SpectralMeasurePVMOperatorValuedProofObligationHandoffBoundary := by
  exact ⟨
    spectral_measure_pvm_operator_valued_proof_obligation_map_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready,
    spectral_measure_pvm_full_axioms_still_open⟩

end

end Theorem
end R4
end MGAP4D