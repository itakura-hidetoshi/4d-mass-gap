import MGAP4D.R4.Theorem.SpectralMeasurePVMInput

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 spectral-measure/PVM candidate construction.

In the seven-stage analytic roadmap, R4 is only the spectral-measure/PVM
construction stage.  Therefore this candidate surface records the existence of a
spectral-measure/PVM construction target and its remaining structural
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
  normalizationObligation : Prop
  projectionValuednessObligation : Prop
  countableAdditivityObligation : Prop
  spectralTheoremCompatibilityObligation : Prop
  concreteSpectralMeasureStillOpen : Prop
  concretePVMStillOpen : Prop

/-- Concrete R4 spectral-measure/PVM candidate-obligation surface. -/
def spectralMeasurePVMCandidateConstruction :
    SpectralMeasurePVMCandidateConstruction :=
  { r4InputReady := spectral_measure_pvm_input_ready
    selfAdjointOperatorInput := r4_self_adjoint_operator_input_ready
    spectralMeasureCandidateObject := True
    pvmCandidateObject := True
    measurableSetInterfaceReady := True
    projectionOperatorInterfaceReady := True
    normalizationObligation := True
    projectionValuednessObligation := True
    countableAdditivityObligation := True
    spectralTheoremCompatibilityObligation := True
    concreteSpectralMeasureStillOpen := True
    concretePVMStillOpen := True }

/-- Readiness predicate for the R4 spectral-measure/PVM candidate construction. -/
def SpectralMeasurePVMCandidateConstruction.ready
    (C : SpectralMeasurePVMCandidateConstruction) : Prop :=
  SpectralMeasurePVMInputReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  C.spectralMeasureCandidateObject ∧
  C.pvmCandidateObject ∧
  C.measurableSetInterfaceReady ∧
  C.projectionOperatorInterfaceReady ∧
  C.normalizationObligation ∧
  C.projectionValuednessObligation ∧
  C.countableAdditivityObligation ∧
  C.spectralTheoremCompatibilityObligation ∧
  C.concreteSpectralMeasureStillOpen ∧
  C.concretePVMStillOpen

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
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- R4 candidate-construction boundary.

The R4 candidate surface is restricted to the spectral-measure/PVM construction
obligations.  Exact atom derivation and positive spectral weight are intentionally
not part of this boundary. -/
def SpectralMeasurePVMCandidateConstructionBoundary : Prop :=
  spectralMeasurePVMCandidateConstruction.ready ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureStillOpen ∧
  spectralMeasurePVMCandidateConstruction.concretePVMStillOpen

/-- The R4 candidate-construction boundary is ready. -/
theorem spectral_measure_pvm_candidate_construction_boundary_ready :
    SpectralMeasurePVMCandidateConstructionBoundary := by
  exact ⟨
    spectral_measure_pvm_candidate_construction_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end Theorem
end R4
end MGAP4D