import MGAP4D.R4.Theorem.SpectralMeasurePVMCandidateConstruction

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Status of an R4 spectral-measure/PVM obligation. -/
inductive SpectralMeasurePVMObligationStatus where
  | registered
  | discharged
  deriving DecidableEq

/-- R4 obligation record for the spectral-measure/PVM stage.

This is bookkeeping, not a proof of the PVM axioms.  It records which
construction obligations are registered and keeps them separate from R6/R7 atom
and positive-weight tasks. -/
structure SpectralMeasurePVMObligationRecord where
  tag : SpectralMeasurePVMObligationTag
  status : SpectralMeasurePVMObligationStatus
  belongsToR4 : Prop
  notR6ExactAtomTask : Prop
  notR7PositiveWeightTask : Prop

/-- Canonical R4 obligation records. -/
def spectralMeasurePVMObligationRecords : List SpectralMeasurePVMObligationRecord :=
  [ { tag := SpectralMeasurePVMObligationTag.normalization
      status := SpectralMeasurePVMObligationStatus.registered
      belongsToR4 := True
      notR6ExactAtomTask := True
      notR7PositiveWeightTask := True },
    { tag := SpectralMeasurePVMObligationTag.projectionValuedness
      status := SpectralMeasurePVMObligationStatus.registered
      belongsToR4 := True
      notR6ExactAtomTask := True
      notR7PositiveWeightTask := True },
    { tag := SpectralMeasurePVMObligationTag.countableAdditivity
      status := SpectralMeasurePVMObligationStatus.registered
      belongsToR4 := True
      notR6ExactAtomTask := True
      notR7PositiveWeightTask := True },
    { tag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
      status := SpectralMeasurePVMObligationStatus.registered
      belongsToR4 := True
      notR6ExactAtomTask := True
      notR7PositiveWeightTask := True },
    { tag := SpectralMeasurePVMObligationTag.concreteSpectralMeasure
      status := SpectralMeasurePVMObligationStatus.registered
      belongsToR4 := True
      notR6ExactAtomTask := True
      notR7PositiveWeightTask := True },
    { tag := SpectralMeasurePVMObligationTag.concretePVM
      status := SpectralMeasurePVMObligationStatus.registered
      belongsToR4 := True
      notR6ExactAtomTask := True
      notR7PositiveWeightTask := True } ]

/-- R4 obligation map readiness.

All R4 PVM/spectral-measure obligations are registered as R4 tasks.  None of
these records is allowed to close R6 exact-atom derivation or R7 positive-weight
nontriviality. -/
def SpectralMeasurePVMObligationMapReady : Prop :=
  spectralMeasurePVMCandidateConstruction.ready ∧
  spectralMeasurePVMObligationRecords.length = 6 ∧
  (∀ r ∈ spectralMeasurePVMObligationRecords,
    r.status = SpectralMeasurePVMObligationStatus.registered ∧
    r.belongsToR4 ∧
    r.notR6ExactAtomTask ∧
    r.notR7PositiveWeightTask)

/-- The R4 spectral-measure/PVM obligation map is ready. -/
theorem spectral_measure_pvm_obligation_map_ready :
    SpectralMeasurePVMObligationMapReady := by
  constructor
  · exact spectral_measure_pvm_candidate_construction_ready
  constructor
  · native_decide
  · intro r hr
    simp [spectralMeasurePVMObligationRecords] at hr
    rcases hr with h | h | h | h | h | h
    · subst r
      exact ⟨rfl, trivial, trivial, trivial⟩
    · subst r
      exact ⟨rfl, trivial, trivial, trivial⟩
    · subst r
      exact ⟨rfl, trivial, trivial, trivial⟩
    · subst r
      exact ⟨rfl, trivial, trivial, trivial⟩
    · subst r
      exact ⟨rfl, trivial, trivial, trivial⟩
    · subst r
      exact ⟨rfl, trivial, trivial, trivial⟩

/-- R4 obligation-map boundary. -/
def SpectralMeasurePVMObligationMapBoundary : Prop :=
  SpectralMeasurePVMObligationMapReady ∧
  SpectralMeasurePVMInputReady

/-- The R4 obligation-map boundary is ready. -/
theorem spectral_measure_pvm_obligation_map_boundary_ready :
    SpectralMeasurePVMObligationMapBoundary := by
  exact ⟨spectral_measure_pvm_obligation_map_ready, spectral_measure_pvm_input_ready⟩

end

end Theorem
end R4
end MGAP4D