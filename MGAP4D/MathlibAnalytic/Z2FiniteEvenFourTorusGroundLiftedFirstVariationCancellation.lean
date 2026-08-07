import MGAP4D.MathlibAnalytic.FiniteLinearizedGroundLiftedDefectFirstVariation
import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementKernelCancellation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationSpatialDefect
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The beta-zero finite Z₂ one-slab kernel first variation has right-boundary
differences independent of the left boundary.  This is the exact finite Wilson
form of boundary additivity after uniform temporal-link averaging. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right_independent
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B B' A A' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B A -
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B A' =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B' A -
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B' A' := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right]

/-- Consequently the unnormalized beta-zero kernel first variation has no
uniform-average complement-to-complement block. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_doubleCentered_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun B A : FiniteEvenFourTorusZ2SliceConfiguration H =>
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
              H energyIdentity energyNontrivial B A)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) = 0 := by
  exact
    finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_eq_zero
      (fun B A : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B A)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right_independent
        H energyIdentity energyNontrivial)

/-- Proof-free first-variation model for a scalar-normalized one-slab kernel at
beta zero.

If a scalar normalization `ν(β)` is differentiable at zero, then by the product
rule its kernel first variation has exactly this form with
`ν₀ = ν(0)` and `ν₁ = ν'(0)`, because the beta-zero unnormalized kernel is the
constant-one kernel.  We deliberately keep `ν₀,ν₁` arbitrary here, so no
unproved differentiability of the operator norm is imported. -/
noncomputable def finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ : ℝ)
    (B A : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ν₀ *
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
        H energyIdentity energyNontrivial B A +
    ν₁

/-- Scalar normalization cannot create a left/right interaction at first order:
right-boundary differences of the normalized first-variation model remain
independent of the left boundary. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_sub_right_independent
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ : ℝ)
    (B B' A A' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ B A -
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ B A' =
    finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ B' A -
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ B' A' := by
  unfold finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right_independent
      H energyIdentity energyNontrivial B B' A A'
  linear_combination ν₀ * h

/-- Exact first-order cancellation for every scalar-normalization product-rule
model:

`Q T₁ Q = 0`.

The normalization derivative contributes only a constant-one kernel and is
therefore killed by double centering as well. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_doubleCentered_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
            H energyIdentity energyNontrivial ν₀ ν₁)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) = 0 := by
  exact
    finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_eq_zero
      (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
        H energyIdentity energyNontrivial ν₀ ν₁)
      (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_sub_right_independent
        H energyIdentity energyNontrivial ν₀ ν₁)

/-- Generic consequence of the Package-T reduction: if the transfer first
variation has zero complement-to-complement block, then the ground-lifted defect
has zero first variation. -/
theorem FiniteLinearizedTransferGroundProjectorData.groundLiftedVariation_eq_zero_of_complementedTransferVariation_eq_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : FiniteLinearizedTransferGroundProjectorData E)
    (hzero :
      D.baseComplement.comp
        (D.transferVariation.comp D.baseComplement) = 0) :
    D.groundLiftedVariation = 0 := by
  rw [D.groundLiftedVariation_eq_neg_baseComplement_comp_transferVariation_comp_baseComplement,
    hzero]
  simp

/-- Any valid linearized ground-projector/transfer data whose beta-zero
projector is uniform averaging and whose transfer first variation is a scalar-
normalized finite Z₂ one-slab product-rule model has identically zero
first-order ground-lifted defect.

This is a conditional algebraic bridge: it does not assert differentiability of
the actual operator norm or moving spectral projector. -/
theorem finiteEvenFourTorusZ2GroundLiftedVariation_eq_zero_of_normalizedKernelFirstVariationModel
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ : ℝ)
    (D : FiniteLinearizedTransferGroundProjectorData
      (FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)))
    (hProjector :
      D.baseProjector =
        (finiteUniformAverageProjectorLinearMap :
          FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
            FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)))
    (hTransferVariation :
      D.transferVariation =
        (finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
            H energyIdentity energyNontrivial ν₀ ν₁)).toLinearMap) :
    D.groundLiftedVariation = 0 := by
  have hComplement :
      D.baseComplement =
        (finiteUniformAverageComplementLinearMap :
          FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
            FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)) := by
    unfold FiniteLinearizedTransferGroundProjectorData.baseComplement
      finiteUniformAverageComplementLinearMap
    rw [hProjector]
  apply D.groundLiftedVariation_eq_zero_of_complementedTransferVariation_eq_zero
  rw [hComplement, hTransferVariation]
  exact
    finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_doubleCentered_eq_zero
      H energyIdentity energyNontrivial ν₀ ν₁

/-- Audit-visible actual-Z₂ first-order cancellation receipt. -/
structure Z2FiniteEvenFourTorusGroundLiftedFirstVariationCancellationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) where
  rawKernelDoubleCentered :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun B A : FiniteEvenFourTorusZ2SliceConfiguration H =>
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
              H energyIdentity energyNontrivial B A)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) = 0
  normalizedModelDoubleCentered :
    ∀ ν₀ ν₁ : ℝ,
      finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
              H energyIdentity energyNontrivial ν₀ ν₁)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap) = 0

/-- Construct the actual-Z₂ Package-T first-order cancellation receipt. -/
noncomputable def z2FiniteEvenFourTorusGroundLiftedFirstVariationCancellationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Z2FiniteEvenFourTorusGroundLiftedFirstVariationCancellationPackage
      H energyIdentity energyNontrivial where
  rawKernelDoubleCentered :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_doubleCentered_eq_zero
      H energyIdentity energyNontrivial
  normalizedModelDoubleCentered := fun ν₀ ν₁ =>
    finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_doubleCentered_eq_zero
      H energyIdentity energyNontrivial ν₀ ν₁

end

end MathlibAnalytic
end MGAP4D
