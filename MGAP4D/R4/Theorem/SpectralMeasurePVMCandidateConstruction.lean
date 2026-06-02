import MGAP4D.R4.Theorem.SpectralMeasurePVMInput

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Open R4 obligations for the spectral-measure/PVM stage.

These are tags, not proofs.  A candidate surface may register these targets
without claiming that normalization, projection-valuedness, countable additivity,
or spectral-theorem compatibility has been proved. -/
inductive SpectralMeasurePVMObligationTag where
  | normalization
  | projectionValuedness
  | countableAdditivity
  | spectralTheoremCompatibility
  | concreteSpectralMeasure
  | concretePVM
  deriving DecidableEq

/-- R4 spectral-measure/PVM candidate construction.

In the seven-stage analytic roadmap, R4 is only the spectral-measure/PVM
construction stage.  Therefore this candidate surface records the existence of a
spectral-measure/PVM construction target and the tags of its remaining structural
obligations.  It deliberately does not mention the exact atom `33 / 20`, atom
membership, projection mass positivity, or positive spectral weight; those belong
to R6 and R7. -/
structure SpectralMeasurePVMCandidateConstruction where
  r4InputReady : SpectralMeasurePVMInputReady
  selfAdjointOperatorInput :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap
  spectralMeasureCandidateObject : Prop
  pvmCandidateObject : Prop
  measurableSetInterfaceReady : Prop
  projectionOperatorInterfaceReady : Prop
  normalizationObligation : SpectralMeasurePVMObligationTag
  projectionValuednessObligation : SpectralMeasurePVMObligationTag
  countableAdditivityObligation : SpectralMeasurePVMObligationTag
  spectralTheoremCompatibilityObligation : SpectralMeasurePVMObligationTag
  concreteSpectralMeasureObligation : SpectralMeasurePVMObligationTag
  concretePVMObligation : SpectralMeasurePVMObligationTag

/-- Concrete R4 spectral-measure/PVM candidate-obligation surface. -/
def spectralMeasurePVMCandidateConstruction :
    SpectralMeasurePVMCandidateConstruction :=
  { r4InputReady := spectral_measure_pvm_input_ready
    selfAdjointOperatorInput := r4_self_adjoint_operator_input_ready
    spectralMeasureCandidateObject := True
    pvmCandidateObject := True
    measurableSetInterfaceReady := True
    projectionOperatorInterfaceReady := True
    normalizationObligation := SpectralMeasurePVMObligationTag.normalization
    projectionValuednessObligation := SpectralMeasurePVMObligationTag.projectionValuedness
    countableAdditivityObligation := SpectralMeasurePVMObligationTag.countableAdditivity
    spectralTheoremCompatibilityObligation := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
    concreteSpectralMeasureObligation := SpectralMeasurePVMObligationTag.concreteSpectralMeasure
    concretePVMObligation := SpectralMeasurePVMObligationTag.concretePVM }

/-- Readiness predicate for the R4 spectral-measure/PVM candidate construction.

This proves only that the R4 candidate objects and obligation targets are
registered.  It does not prove the obligations themselves. -/
def SpectralMeasurePVMCandidateConstruction.ready
    (C : SpectralMeasurePVMCandidateConstruction) : Prop :=
  SpectralMeasurePVMInputReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  C.spectralMeasureCandidateObject ∧
  C.pvmCandidateObject ∧
  C.measurableSetInterfaceReady ∧
  C.projectionOperatorInterfaceReady ∧
  C.normalizationObligation = SpectralMeasurePVMObligationTag.normalization ∧
  C.projectionValuednessObligation = SpectralMeasurePVMObligationTag.projectionValuedness ∧
  C.countableAdditivityObligation = SpectralMeasurePVMObligationTag.countableAdditivity ∧
  C.spectralTheoremCompatibilityObligation =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  C.concreteSpectralMeasureObligation =
    SpectralMeasurePVMObligationTag.concreteSpectralMeasure ∧
  C.concretePVMObligation = SpectralMeasurePVMObligationTag.concretePVM

/-- The R4 spectral-measure/PVM candidate-obligation surface is ready. -/
theorem spectral_measure_pvm_candidate_construction_ready :
    spectralMeasurePVMCandidateConstruction.ready := by
  exact ⟨
    spectral_measure_pvm_input_ready,
    r4_self_adjoint_operator_input_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- R4 candidate-construction boundary.

The R4 candidate surface is restricted to spectral-measure/PVM construction
objects plus open obligation tags.  Exact atom derivation and positive spectral
weight are intentionally not part of this boundary. -/
def SpectralMeasurePVMCandidateConstructionBoundary : Prop :=
  spectralMeasurePVMCandidateConstruction.ready ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureObligation =
    SpectralMeasurePVMObligationTag.concreteSpectralMeasure ∧
  spectralMeasurePVMCandidateConstruction.concretePVMObligation =
    SpectralMeasurePVMObligationTag.concretePVM

/-- The R4 candidate-construction boundary is ready. -/
theorem spectral_measure_pvm_candidate_construction_boundary_ready :
    SpectralMeasurePVMCandidateConstructionBoundary := by
  exact ⟨
    spectral_measure_pvm_candidate_construction_ready,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

end

end Theorem
end R4
end MGAP4D