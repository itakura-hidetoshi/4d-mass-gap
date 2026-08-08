import MGAP4D.MathlibAnalytic.NonzeroSecondOrderSmallPositive
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossingSecondMomentWitnessPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A coordinatewise realized second-order family of finite-boundary linear
maps.  The coefficient `L₂` uses the same non-factorial second-variation
convention as Package U/X.

This structure is deliberately a realization hypothesis: it does not assert
that the actual operator-norm normalization or moving ground spectral projector
has already been proved twice differentiable. -/
structure FiniteBoundarySecondOrderFamilyRealization
    (α : Type) [Fintype α] [Nonempty α]
    (L₂ : FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α) where
  family : ℝ → FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α
  coordinateExpansion :
    ∀ f : FiniteBoundaryHilbert α, ∀ y : α,
      HasSecondOrderExpansionAtZero
        (fun β : ℝ => family β f y)
        (L₂ f y)

/-- A nonzero finite-boundary linear map has a nonzero scalar matrix
coefficient after choosing one input vector and one output coordinate. -/
theorem finiteBoundaryLinearMap_exists_input_coordinate_ne_zero
    {α : Type} [Fintype α] [Nonempty α]
    (L : FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α)
    (hL : L ≠ 0) :
    ∃ f : FiniteBoundaryHilbert α, ∃ y : α, L f y ≠ 0 := by
  by_contra h
  push_neg at h
  apply hL
  apply LinearMap.ext
  intro f
  ext y
  exact h f y

/-- Operator-valued second-order small-positive criterion on a finite boundary.
A nonzero second variation together with coordinatewise realized Peano
expansions forces the whole linear-map family to be nonzero throughout a
sufficiently small positive interval. -/
theorem FiniteBoundarySecondOrderFamilyRealization.exists_pos_forall_pos_lt_family_ne_zero
    {α : Type} [Fintype α] [Nonempty α]
    {L₂ : FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α}
    (R : FiniteBoundarySecondOrderFamilyRealization α L₂)
    (hL₂ : L₂ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, 0 < β → β < ε → R.family β ≠ 0 := by
  rcases finiteBoundaryLinearMap_exists_input_coordinate_ne_zero L₂ hL₂ with
    ⟨f, y, hfy⟩
  rcases
      (R.coordinateExpansion f y).exists_pos_forall_pos_lt_ne_zero_of_secondVariation_ne_zero
        hfy with
    ⟨ε, hε, hcoord⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε hzero
  apply hcoord β hβ hβε
  simp [hzero]

/-- Package-X plus the generic second-order criterion: under the strict
physical energy ordering, every realized family whose second coefficient is
the complemented ground-lifted Package-X second variation is nonzero on a
whole sufficiently small positive interval.

This is conditional only on the displayed Package-W product-rule models and on
`R.coordinateExpansion`.  In particular it does not smuggle in the still-open
second differentiability of the actual operator norm normalization or moving
ground spectral projector. -/
theorem finiteEvenFourTorusZ2GroundLiftedSecondOrderFamily_exists_smallPositive_interval_ne_zero_zero_of_models
    (energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (D : FiniteSecondOrderLinearizedTransferGroundProjectorData
      (FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration 0)))
    (hProjector :
      D.baseProjector =
        (finiteUniformAverageProjectorLinearMap :
          FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration 0) →ₗ[ℝ]
            FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration 0)))
    (hTransferVariation :
      D.transferVariation =
        (finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
            0 energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹
            normalizationDerivative)).toLinearMap)
    (hTransferSecondVariation :
      D.transferSecondVariation =
        (finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
            0 energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹
            normalizationDerivative normalizationSecondDerivative)).toLinearMap)
    (R : FiniteBoundarySecondOrderFamilyRealization
      (FiniteEvenFourTorusZ2SliceConfiguration 0)
      (D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement))) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, 0 < β → β < ε → R.family β ≠ 0 := by
  apply R.exists_pos_forall_pos_lt_family_ne_zero
  exact
    finiteEvenFourTorusZ2GroundLiftedSecondVariation_ne_zero_zero_of_models
      energyIdentity energyNontrivial normalizationDerivative
      normalizationSecondDerivative hEnergy D hProjector hTransferVariation
      hTransferSecondVariation

/-- Audit-visible Package-Y receipt.  It records exactly the remaining analytic
hinge after Package X: once the actual complemented ground-lifted departure is
realized coordinatewise to second order, the already-proved nonzero Package-X
second variation gives positive-coupling nonvanishing on an interval. -/
structure Z2FiniteEvenFourTorusGroundLiftedSecondOrderSmallPositivePackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  smallPositiveOfRealization :
    ∀ normalizationDerivative normalizationSecondDerivative : ℝ,
      ∀ D : FiniteSecondOrderLinearizedTransferGroundProjectorData
        (FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration 0)),
      D.baseProjector =
          (finiteUniformAverageProjectorLinearMap :
            FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration 0) →ₗ[ℝ]
              FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration 0)) →
      D.transferVariation =
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
              0 energyIdentity energyNontrivial
              (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹
              normalizationDerivative)).toLinearMap →
      D.transferSecondVariation =
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
              0 energyIdentity energyNontrivial
              (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹
              normalizationDerivative normalizationSecondDerivative)).toLinearMap →
      ∀ R : FiniteBoundarySecondOrderFamilyRealization
        (FiniteEvenFourTorusZ2SliceConfiguration 0)
        (D.baseComplement.comp
          (D.groundLiftedSecondVariation.comp D.baseComplement)),
        ∃ ε : ℝ, 0 < ε ∧
          ∀ β : ℝ, 0 < β → β < ε → R.family β ≠ 0

/-- Construct the Package-Y conditional second-order small-positive receipt. -/
noncomputable def z2FiniteEvenFourTorusGroundLiftedSecondOrderSmallPositivePackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusGroundLiftedSecondOrderSmallPositivePackage
      energyIdentity energyNontrivial hEnergy where
  smallPositiveOfRealization :=
    fun normalizationDerivative normalizationSecondDerivative D hProjector
        hTransferVariation hTransferSecondVariation R =>
      finiteEvenFourTorusZ2GroundLiftedSecondOrderFamily_exists_smallPositive_interval_ne_zero_zero_of_models
        energyIdentity energyNontrivial normalizationDerivative
        normalizationSecondDerivative hEnergy D hProjector hTransferVariation
        hTransferSecondVariation R

end

end MathlibAnalytic
end MGAP4D
