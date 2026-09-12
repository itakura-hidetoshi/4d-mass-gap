import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Raw pullback of a coarse gauge-invariant configuration wavefunction along
the actual geometric fine-to-coarse `Z₂` configuration map.  This is the
un-normalized configuration-level map underlying the canonical invariant
Hilbert isometry. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) where
  toFun f :=
    ⟨WithLp.toLp 2 fun A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) =>
        f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A), by
      intro g A
      change
        f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H (g • A)) =
          f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)
      rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
      exact f.2
        (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H g)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)⟩
  map_add' f g := by
    apply Subtype.ext
    ext A
    rfl
  map_smul' c f := by
    apply Subtype.ext
    ext A
    rfl

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap_apply
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H f).1 A =
      f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) :=
  rfl

/-- Exact norm preservation of the canonical normalized invariant embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_norm
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f‖ = ‖f‖ :=
  (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).norm_map f

/-- Exact norm preservation of the direct two-step invariant embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_norm
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f‖ = ‖f‖ :=
  (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).norm_map f

/-- Configuration-level evaluation of the actual one-step transfer residual.
The first term evolves the normalized embedded coarse state with the actual
fine unfixed-gauge one-slab transfer; the second embeds the actual coarse
invariant one-slab evolution. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_apply_coe
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f).1 A -
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f)).1 A := by
  rfl

/-- Configuration-level evaluation of the direct two-step transfer residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_apply_coe
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f).1 A -
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f)).1 A := by
  rfl

/-- The norm of the Package-E one-step orbit obstruction on canonical orbit
coordinates is exactly the norm of the actual invariant-configuration residual.
This upgrades the existing vector equality to an audit-visible quantitative
identity. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_norm
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)‖ =
      ‖finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f‖ := by
  rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual]
  exact
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement H)).forward.norm_map _

/-- The corresponding exact norm identity for the direct two-step obstruction. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_forward_norm
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)‖ =
      ‖finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f‖ := by
  rw [finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual]
  exact
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))).forward.norm_map _

/-- Audit-visible final evaluation layer for Package F.  It records the raw
configuration pullback, normalized one/two-step embeddings, pointwise transfer
residual evaluations, and exact orbit/invariant obstruction norm identities. -/
structure Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorEvaluationPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  rawPullback :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  rawPullback_eq : rawPullback =
    finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H
  oneStepNorm : ∀ f,
    ‖finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f‖ = ‖f‖
  twoStepNorm : ∀ f,
    ‖finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f‖ = ‖f‖
  oneStepObstructionNorm : ∀ f,
    ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)‖ =
      ‖finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f‖
  twoStepObstructionNorm : ∀ f,
    ‖finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)‖ =
      ‖finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f‖

/-- Construct the final actual geometric evaluation receipt for Package F. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeGeometricOperatorEvaluationPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorEvaluationPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  rawPullback := finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H
  rawPullback_eq := rfl
  oneStepNorm := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_norm H
  twoStepNorm := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_norm H
  oneStepObstructionNorm :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_norm
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepObstructionNorm :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_forward_norm
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
