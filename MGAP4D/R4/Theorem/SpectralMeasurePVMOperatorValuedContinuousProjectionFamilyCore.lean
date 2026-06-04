import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Continuous-linear-map projection family indexed by the current two-index R4
spectral index surface. -/
def spectralMeasurePVMContinuousProjectionFamily
    (i : SpectralMeasurePVMConcreteIndex) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
    (spectralMeasurePVMHilbertProjectionSlotFromIndex i)

/-- Empty index gives the zero continuous projection. -/
theorem spectral_measure_pvm_continuous_projection_family_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily SpectralMeasurePVMConcreteIndex.empty x = 0 := by
  rfl

/-- Whole index gives the identity continuous projection. -/
theorem spectral_measure_pvm_continuous_projection_family_whole_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily SpectralMeasurePVMConcreteIndex.whole x = x := by
  rfl

/-- Pointwise idempotence of the continuous projection family. -/
theorem spectral_measure_pvm_continuous_projection_family_pointwise_idempotent
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily i
        (spectralMeasurePVMContinuousProjectionFamily i x) =
      spectralMeasurePVMContinuousProjectionFamily i x := by
  cases i <;> rfl

/-- Disjoint continuous projections annihilate pointwise on the current two-index
surface. -/
theorem spectral_measure_pvm_continuous_projection_family_disjoint_pointwise_zero
    (i j : SpectralMeasurePVMConcreteIndex)
    (hij : SpectralMeasurePVMConcreteIndexDisjoint i j)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily i
        (spectralMeasurePVMContinuousProjectionFamily j x) = 0 := by
  cases i <;> cases j <;> try rfl
  exact False.elim hij

/-- Reversed disjoint continuous projections annihilate pointwise on the current
two-index surface. -/
theorem spectral_measure_pvm_continuous_projection_family_disjoint_reversed_pointwise_zero
    (i j : SpectralMeasurePVMConcreteIndex)
    (hij : SpectralMeasurePVMConcreteIndexDisjoint i j)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily j
        (spectralMeasurePVMContinuousProjectionFamily i x) = 0 := by
  cases i <;> cases j <;> try rfl
  exact False.elim hij

/-- Pointwise finite additivity for disjoint empty/whole continuous projections.
This is still the two-index R4 surface, not a genuine Borel PVM. -/
theorem spectral_measure_pvm_continuous_projection_family_binary_additivity_apply
    (i j : SpectralMeasurePVMConcreteIndex)
    (hij : SpectralMeasurePVMConcreteIndexDisjoint i j)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousProjectionFamily
        (SpectralMeasurePVMConcreteIndexUnion i j) x =
      spectralMeasurePVMContinuousProjectionFamily i x +
        spectralMeasurePVMContinuousProjectionFamily j x := by
  cases i <;> cases j <;> simp [spectralMeasurePVMContinuousProjectionFamily,
    SpectralMeasurePVMConcreteIndexUnion,
    spectralMeasurePVMHilbertProjectionSlotFromIndex,
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap]
  exact False.elim hij

/-- Normalization target for the continuous projection family. -/
def SpectralMeasurePVMContinuousProjectionFamilyNormalizationTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousProjectionFamily SpectralMeasurePVMConcreteIndex.empty x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousProjectionFamily SpectralMeasurePVMConcreteIndex.whole x = x)

/-- Pointwise projection-valuedness target for the continuous projection family. -/
def SpectralMeasurePVMContinuousProjectionFamilyProjectionValuednessTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousProjectionFamily i
          (spectralMeasurePVMContinuousProjectionFamily i x) =
        spectralMeasurePVMContinuousProjectionFamily i x

/-- Pointwise orthogonality target for disjoint continuous projections. -/
def SpectralMeasurePVMContinuousProjectionFamilyOrthogonalityTarget : Prop :=
  ∀ i j : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteIndexDisjoint i j →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousProjectionFamily i
            (spectralMeasurePVMContinuousProjectionFamily j x) = 0

/-- Pointwise finite-additivity target for the continuous projection family. -/
def SpectralMeasurePVMContinuousProjectionFamilyFiniteAdditivityTarget : Prop :=
  ∀ i j : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteIndexDisjoint i j →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousProjectionFamily
            (SpectralMeasurePVMConcreteIndexUnion i j) x =
          spectralMeasurePVMContinuousProjectionFamily i x +
            spectralMeasurePVMContinuousProjectionFamily j x

/-- Self-adjoint spectral-measure projection upgrade remains open. -/
def SpectralMeasurePVMContinuousProjectionFamilySelfAdjointPVMUpgradeStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R4 continuous projection family core. -/
def SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapCoreReady ∧
  SpectralMeasurePVMContinuousProjectionFamilyNormalizationTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilyProjectionValuednessTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilyOrthogonalityTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilyFiniteAdditivityTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilySelfAdjointPVMUpgradeStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The continuous projection-family normalization target is ready. -/
theorem spectral_measure_pvm_continuous_projection_family_normalization_target_ready :
    SpectralMeasurePVMContinuousProjectionFamilyNormalizationTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_projection_family_empty_apply,
    spectral_measure_pvm_continuous_projection_family_whole_apply⟩

/-- The continuous projection-family projection-valuedness target is ready. -/
theorem spectral_measure_pvm_continuous_projection_family_projection_valuedness_target_ready :
    SpectralMeasurePVMContinuousProjectionFamilyProjectionValuednessTarget := by
  exact spectral_measure_pvm_continuous_projection_family_pointwise_idempotent

/-- The continuous projection-family orthogonality target is ready. -/
theorem spectral_measure_pvm_continuous_projection_family_orthogonality_target_ready :
    SpectralMeasurePVMContinuousProjectionFamilyOrthogonalityTarget := by
  exact spectral_measure_pvm_continuous_projection_family_disjoint_pointwise_zero

/-- The continuous projection-family finite-additivity target is ready. -/
theorem spectral_measure_pvm_continuous_projection_family_finite_additivity_target_ready :
    SpectralMeasurePVMContinuousProjectionFamilyFiniteAdditivityTarget := by
  exact spectral_measure_pvm_continuous_projection_family_binary_additivity_apply

/-- The self-adjoint PVM upgrade remains explicitly open. -/
theorem spectral_measure_pvm_continuous_projection_family_self_adjoint_pvm_upgrade_still_open_ready :
    SpectralMeasurePVMContinuousProjectionFamilySelfAdjointPVMUpgradeStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The R4 continuous projection family core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_projection_family_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_hilbert_projection_continuous_linear_map_core_ready,
    spectral_measure_pvm_continuous_projection_family_normalization_target_ready,
    spectral_measure_pvm_continuous_projection_family_projection_valuedness_target_ready,
    spectral_measure_pvm_continuous_projection_family_orthogonality_target_ready,
    spectral_measure_pvm_continuous_projection_family_finite_additivity_target_ready,
    spectral_measure_pvm_continuous_projection_family_self_adjoint_pvm_upgrade_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous projection family core. -/
def SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyCoreReady ∧
  SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapBoundaryHeld ∧
  SpectralMeasurePVMContinuousProjectionFamilySelfAdjointPVMUpgradeStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous projection family boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_projection_family_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_projection_family_core_ready,
    spectral_measure_pvm_operator_valued_hilbert_projection_continuous_linear_map_boundary_held,
    spectral_measure_pvm_continuous_projection_family_self_adjoint_pvm_upgrade_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
