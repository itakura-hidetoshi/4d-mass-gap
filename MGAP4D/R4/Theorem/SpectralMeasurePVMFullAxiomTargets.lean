import MGAP4D.R4.Theorem.SpectralMeasurePVMStructuralShellCompletion

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A full R4 PVM axiom target.

`statement` is the future mathematical statement to be proved; `discharge` is a
separate witness slot.  In the current R4 layer we register targets without
claiming discharge. -/
structure SpectralMeasurePVMFullAxiomTarget where
  tag : SpectralMeasurePVMObligationTag
  statement : Prop
  discharge : Prop
  registeredByStructuralShell : Prop
  notExactAtomDerivation : Prop
  notPositiveWeightDerivation : Prop

/-- The full-normalization target for a genuine PVM.

The current skeleton does not prove `E(ℝ) = I`; it registers that target. -/
def spectralMeasurePVMNormalizationFullTarget :
    SpectralMeasurePVMFullAxiomTarget :=
  { tag := SpectralMeasurePVMObligationTag.normalization
    statement := True
    discharge := False
    registeredByStructuralShell := SpectralMeasurePVMStructuralShellCompleted
    notExactAtomDerivation := True
    notPositiveWeightDerivation := True }

/-- The full projection-valuedness target for a genuine PVM. -/
def spectralMeasurePVMProjectionValuednessFullTarget :
    SpectralMeasurePVMFullAxiomTarget :=
  { tag := SpectralMeasurePVMObligationTag.projectionValuedness
    statement := True
    discharge := False
    registeredByStructuralShell := SpectralMeasurePVMStructuralShellCompleted
    notExactAtomDerivation := True
    notPositiveWeightDerivation := True }

/-- The full countable-additivity target for a genuine PVM. -/
def spectralMeasurePVMCountableAdditivityFullTarget :
    SpectralMeasurePVMFullAxiomTarget :=
  { tag := SpectralMeasurePVMObligationTag.countableAdditivity
    statement := True
    discharge := False
    registeredByStructuralShell := SpectralMeasurePVMStructuralShellCompleted
    notExactAtomDerivation := True
    notPositiveWeightDerivation := True }

/-- The full spectral-theorem compatibility target. -/
def spectralMeasurePVMSpectralTheoremCompatibilityFullTarget :
    SpectralMeasurePVMFullAxiomTarget :=
  { tag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
    statement := True
    discharge := False
    registeredByStructuralShell := SpectralMeasurePVMStructuralShellCompleted
    notExactAtomDerivation := True
    notPositiveWeightDerivation := True }

/-- The concrete spectral-measure construction target. -/
def spectralMeasurePVMConcreteSpectralMeasureFullTarget :
    SpectralMeasurePVMFullAxiomTarget :=
  { tag := SpectralMeasurePVMObligationTag.concreteSpectralMeasure
    statement := True
    discharge := False
    registeredByStructuralShell := SpectralMeasurePVMStructuralShellCompleted
    notExactAtomDerivation := True
    notPositiveWeightDerivation := True }

/-- The concrete PVM construction target. -/
def spectralMeasurePVMConcretePVMFullTarget :
    SpectralMeasurePVMFullAxiomTarget :=
  { tag := SpectralMeasurePVMObligationTag.concretePVM
    statement := True
    discharge := False
    registeredByStructuralShell := SpectralMeasurePVMStructuralShellCompleted
    notExactAtomDerivation := True
    notPositiveWeightDerivation := True }

/-- Canonical list of full R4 PVM targets. -/
def spectralMeasurePVMFullAxiomTargets : List SpectralMeasurePVMFullAxiomTarget :=
  [ spectralMeasurePVMNormalizationFullTarget,
    spectralMeasurePVMProjectionValuednessFullTarget,
    spectralMeasurePVMCountableAdditivityFullTarget,
    spectralMeasurePVMSpectralTheoremCompatibilityFullTarget,
    spectralMeasurePVMConcreteSpectralMeasureFullTarget,
    spectralMeasurePVMConcretePVMFullTarget ]

/-- Full R4 target registration readiness.

All six targets are registered by the structural shell, and none is discharged at
this stage.  The `False` discharge slots prevent these registrations from being
mistaken for closed full PVM axioms. -/
def SpectralMeasurePVMFullAxiomTargetsRegistered : Prop :=
  SpectralMeasurePVMPublicShellBoundary ∧
  spectralMeasurePVMFullAxiomTargets.length = 6 ∧
  (∀ t ∈ spectralMeasurePVMFullAxiomTargets,
    t.registeredByStructuralShell ∧
    t.notExactAtomDerivation ∧
    t.notPositiveWeightDerivation ∧
    ¬ t.discharge)

/-- The full R4 PVM axiom targets are registered but not discharged. -/
theorem spectral_measure_pvm_full_axiom_targets_registered :
    SpectralMeasurePVMFullAxiomTargetsRegistered := by
  constructor
  · exact spectral_measure_pvm_public_shell_boundary_ready
  constructor
  · native_decide
  · intro t ht
    simp [spectralMeasurePVMFullAxiomTargets,
      spectralMeasurePVMNormalizationFullTarget,
      spectralMeasurePVMProjectionValuednessFullTarget,
      spectralMeasurePVMCountableAdditivityFullTarget,
      spectralMeasurePVMSpectralTheoremCompatibilityFullTarget,
      spectralMeasurePVMConcreteSpectralMeasureFullTarget,
      spectralMeasurePVMConcretePVMFullTarget] at ht
    rcases ht with h | h | h | h | h | h
    · subst t
      exact ⟨spectral_measure_pvm_structural_shell_completed, trivial, trivial, id⟩
    · subst t
      exact ⟨spectral_measure_pvm_structural_shell_completed, trivial, trivial, id⟩
    · subst t
      exact ⟨spectral_measure_pvm_structural_shell_completed, trivial, trivial, id⟩
    · subst t
      exact ⟨spectral_measure_pvm_structural_shell_completed, trivial, trivial, id⟩
    · subst t
      exact ⟨spectral_measure_pvm_structural_shell_completed, trivial, trivial, id⟩
    · subst t
      exact ⟨spectral_measure_pvm_structural_shell_completed, trivial, trivial, id⟩

/-- R4 full-axiom target boundary.

This is the next proof boundary after the structural shell: six full PVM targets
exist as registered goals, while all discharge slots remain closed. -/
def SpectralMeasurePVMFullAxiomTargetBoundary : Prop :=
  SpectralMeasurePVMFullAxiomTargetsRegistered ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMStructuralShellCompleted

/-- The R4 full-axiom target boundary is ready. -/
theorem spectral_measure_pvm_full_axiom_target_boundary_ready :
    SpectralMeasurePVMFullAxiomTargetBoundary := by
  exact ⟨
    spectral_measure_pvm_full_axiom_targets_registered,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_structural_shell_completed⟩

end

end Theorem
end R4
end MGAP4D