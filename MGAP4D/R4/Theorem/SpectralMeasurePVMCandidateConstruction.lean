import MGAP4D.R4.Theorem.SpectralMeasurePVMInput
import MGAP4D.MathlibAnalytic.PVMInterface
import MGAP4D.MathlibAnalytic.SpectralRealizationSkeleton

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 spectral-measure/PVM candidate construction.

This is the first constructive R4 step after the input handoff.  It packages the
concrete exact atom, projection-mass function, and exact-value projection surface
already available in the analytic spine.  It is intentionally a candidate
construction: it does not claim countable additivity, projection-valuedness in the
full Mathlib sense, or the full spectral theorem for the dense `LinearPMap`. -/
structure SpectralMeasurePVMCandidateConstruction where
  r4InputReady : SpectralMeasurePVMInputReady
  spectralSkeletonReady : MathlibAnalytic.spectralRealizationSkeletonReviewSurface.ready
  pvmInterfaceReady : MathlibAnalytic.singletonPVMInterface.ready
  exactAtom : Set ℝ
  exactAtom_eq_singleton : exactAtom = Set.singleton MathlibAnalytic.exactGapValueReal
  exactValueInAtom : MathlibAnalytic.exactGapValueReal ∈ exactAtom
  projectionMass : Set ℝ → ℝ
  projectionMass_eq : projectionMass = MathlibAnalytic.prototypeProjectionMassReal
  exactAtomMassPositive : 0 < projectionMass exactAtom
  exactAtomMassNonzero : projectionMass exactAtom ≠ 0
  exactValueEq3320 : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  spectralProjectionAtExact :
    MathlibAnalytic.prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact
  pvmCandidateConstructed : Prop
  spectralMeasureCandidateConstructed : Prop
  fullPVMTheoremStillOpen : Prop
  countableAdditivityStillOpen : Prop
  projectionValuednessStillOpen : Prop
  concreteSpectralTheoremStillOpen : Prop

/-- Concrete R4 spectral-measure/PVM candidate. -/
def spectralMeasurePVMCandidateConstruction :
    SpectralMeasurePVMCandidateConstruction :=
  { r4InputReady := spectral_measure_pvm_input_ready
    spectralSkeletonReady := MathlibAnalytic.spectral_realization_skeleton_review_surface_ready
    pvmInterfaceReady := MathlibAnalytic.singleton_pvm_interface_ready
    exactAtom := MathlibAnalytic.exactGapAtomReal
    exactAtom_eq_singleton := rfl
    exactValueInAtom := MathlibAnalytic.exactGapValueReal_mem_exactGapAtomReal
    projectionMass := MathlibAnalytic.prototypeProjectionMassReal
    projectionMass_eq := rfl
    exactAtomMassPositive := MathlibAnalytic.prototypeProjectionMassReal_exact_atom_pos
    exactAtomMassNonzero := MathlibAnalytic.prototypeProjectionMassReal_exact_atom_ne_zero
    exactValueEq3320 := MathlibAnalytic.exactGapValueReal_eq
    spectralProjectionAtExact :=
      MathlibAnalytic.prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact_proof
    pvmCandidateConstructed := True
    spectralMeasureCandidateConstructed := True
    fullPVMTheoremStillOpen := True
    countableAdditivityStillOpen := True
    projectionValuednessStillOpen := True
    concreteSpectralTheoremStillOpen := True }

/-- Readiness predicate for the R4 spectral-measure/PVM candidate construction. -/
def SpectralMeasurePVMCandidateConstruction.ready
    (C : SpectralMeasurePVMCandidateConstruction) : Prop :=
  SpectralMeasurePVMInputReady ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.ready ∧
  MathlibAnalytic.singletonPVMInterface.ready ∧
  C.exactAtom = Set.singleton MathlibAnalytic.exactGapValueReal ∧
  MathlibAnalytic.exactGapValueReal ∈ C.exactAtom ∧
  C.projectionMass = MathlibAnalytic.prototypeProjectionMassReal ∧
  0 < C.projectionMass C.exactAtom ∧
  C.projectionMass C.exactAtom ≠ 0 ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MathlibAnalytic.prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact ∧
  C.pvmCandidateConstructed ∧
  C.spectralMeasureCandidateConstructed ∧
  C.fullPVMTheoremStillOpen ∧
  C.countableAdditivityStillOpen ∧
  C.projectionValuednessStillOpen ∧
  C.concreteSpectralTheoremStillOpen

/-- The R4 spectral-measure/PVM candidate construction is ready. -/
theorem spectral_measure_pvm_candidate_construction_ready :
    spectralMeasurePVMCandidateConstruction.ready := by
  exact ⟨
    spectral_measure_pvm_input_ready,
    MathlibAnalytic.spectral_realization_skeleton_review_surface_ready,
    MathlibAnalytic.singleton_pvm_interface_ready,
    rfl,
    MathlibAnalytic.exactGapValueReal_mem_exactGapAtomReal,
    rfl,
    MathlibAnalytic.prototypeProjectionMassReal_exact_atom_pos,
    MathlibAnalytic.prototypeProjectionMassReal_exact_atom_ne_zero,
    MathlibAnalytic.exactGapValueReal_eq,
    MathlibAnalytic.prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact_proof,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- R4 candidate-construction boundary.

The exact-atom spectral-measure/PVM candidate is constructed.  The remaining R4
work is to replace this candidate surface by a full Mathlib spectral theorem/PVM
construction for the dense self-adjoint `LinearPMap`. -/
def SpectralMeasurePVMCandidateConstructionBoundary : Prop :=
  spectralMeasurePVMCandidateConstruction.ready ∧
  spectralMeasurePVMCandidateConstruction.fullPVMTheoremStillOpen ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityStillOpen ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessStillOpen ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralTheoremStillOpen

/-- The R4 candidate-construction boundary is ready. -/
theorem spectral_measure_pvm_candidate_construction_boundary_ready :
    SpectralMeasurePVMCandidateConstructionBoundary := by
  exact ⟨
    spectral_measure_pvm_candidate_construction_ready,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end Theorem
end R4
end MGAP4D