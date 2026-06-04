import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Continuous-projection realization of the all-empty countable union branch.
This is still the two-index R4 surface: it does not assert a genuine countable
operator-topology sum. -/
def spectralMeasurePVMContinuousProjectionCountableUnionAllEmpty
    (s : SpectralMeasurePVMConcreteCountableFamily) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMContinuousProjectionFamily
    (SpectralMeasurePVMConcreteCountableUnionAllEmpty s)

/-- Continuous-projection realization of the pinned single-whole countable union
branch. -/
def spectralMeasurePVMContinuousProjectionCountableUnionSingleWholeAt
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMContinuousProjectionFamily
    (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k)

/-- The all-empty countable branch acts as zero on the Hilbert carrier. -/
theorem spectral_measure_pvm_continuous_projection_countable_all_empty_apply
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (_hs : SpectralMeasurePVMConcreteAllEmptyFamily s)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionCountableUnionAllEmpty s x = 0 := by
  rfl

/-- The pinned single-whole countable branch acts as identity on the Hilbert carrier. -/
theorem spectral_measure_pvm_continuous_projection_countable_single_whole_apply
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (_hs : SpectralMeasurePVMConcreteSingleWholeAt s k)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionCountableUnionSingleWholeAt s k x = x := by
  rfl

/-- All finite partial unions of an all-empty family act as zero on the Hilbert
carrier. -/
theorem spectral_measure_pvm_continuous_projection_all_empty_partial_apply
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s)
    (N : Nat)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily
        (SpectralMeasurePVMConcreteFinitePartialUnion N s) x = 0 := by
  rw [spectral_measure_pvm_concrete_partial_union_all_empty s hs N]
  rfl

/-- Countable branch target for the continuous projection family. -/
def SpectralMeasurePVMContinuousProjectionCountableBranchTarget : Prop :=
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    SpectralMeasurePVMConcreteAllEmptyFamily s →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousProjectionCountableUnionAllEmpty s x = 0) ∧
  (∀ s : SpectralMeasurePVMConcreteCountableFamily,
    ∀ k : Nat,
      SpectralMeasurePVMConcreteSingleWholeAt s k →
        ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
          spectralMeasurePVMContinuousProjectionCountableUnionSingleWholeAt s k x = x)

/-- Finite partial branch target for all-empty countable families. -/
def SpectralMeasurePVMContinuousProjectionFinitePartialAllEmptyTarget : Prop :=
  ∀ s : SpectralMeasurePVMConcreteCountableFamily,
    SpectralMeasurePVMConcreteAllEmptyFamily s →
      ∀ N : Nat,
        ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
          spectralMeasurePVMContinuousProjectionFamily
              (SpectralMeasurePVMConcreteFinitePartialUnion N s) x = 0

/-- Genuine countable operator-topology additivity remains open after the current
continuous-projection countable branches. -/
def SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R4 continuous projection countable branch core. -/
def SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyCoreReady ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMContinuousProjectionCountableBranchTarget ∧
  SpectralMeasurePVMContinuousProjectionFinitePartialAllEmptyTarget ∧
  SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The continuous projection countable branch target is ready. -/
theorem spectral_measure_pvm_continuous_projection_countable_branch_target_ready :
    SpectralMeasurePVMContinuousProjectionCountableBranchTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_projection_countable_all_empty_apply,
    spectral_measure_pvm_continuous_projection_countable_single_whole_apply⟩

/-- The continuous projection finite partial all-empty target is ready. -/
theorem spectral_measure_pvm_continuous_projection_finite_partial_all_empty_target_ready :
    SpectralMeasurePVMContinuousProjectionFinitePartialAllEmptyTarget := by
  intro s hs N x
  exact spectral_measure_pvm_continuous_projection_all_empty_partial_apply s hs N x

/-- Genuine countable operator-topology additivity remains explicitly open. -/
theorem spectral_measure_pvm_continuous_projection_genuine_countable_additivity_still_open_ready :
    SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The R4 continuous projection countable branch core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_projection_family_core_ready,
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_continuous_projection_countable_branch_target_ready,
    spectral_measure_pvm_continuous_projection_finite_partial_all_empty_target_ready,
    spectral_measure_pvm_continuous_projection_genuine_countable_additivity_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous projection countable branch core. -/
def SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyBoundaryHeld ∧
  SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous projection countable branch boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_core_ready,
    spectral_measure_pvm_operator_valued_continuous_projection_family_boundary_held,
    spectral_measure_pvm_continuous_projection_genuine_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
