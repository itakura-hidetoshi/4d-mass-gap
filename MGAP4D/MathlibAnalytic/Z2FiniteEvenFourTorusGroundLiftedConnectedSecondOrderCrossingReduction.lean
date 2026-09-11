import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellation
import MGAP4D.MathlibAnalytic.FiniteLinearizedGroundLiftedDefectSecondVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact beta-zero normalization of the temporal crossing second moment by the
boundary configuration cardinality. -/
noncomputable def finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment
      H energyIdentity energyNontrivial A B

/-- Kernel containing exactly the two interaction pieces surviving the raw
second-moment double centering before the ground-projector correction. -/
noncomputable def finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
      H energyIdentity energyNontrivial A B +
    finiteUniformNormalizedSpatialRankOneKernel
      (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial X)
      A B

/-- Removing the Package-V interaction kernel from the raw one-slab second
variation leaves only boundary-additive terms. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_sub_interaction_sub_right_independent
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A' B B' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial A B -
        finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
          H energyIdentity energyNontrivial A B) -
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial A B' -
        finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
          H energyIdentity energyNontrivial A B') =
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial A' B -
        finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
          H energyIdentity energyNontrivial A' B) -
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial A' B' -
        finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
          H energyIdentity energyNontrivial A' B') := by
  let left : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
    fun X => (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial X
  let right : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ := left
  let crossing : FiniteEvenFourTorusZ2TemporalLinkField H →
      FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
    fun U X Y => finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
      H 0 energyIdentity energyNontrivial U X Y
  let crossingMean :=
    finiteEvenFourTorusZ2TemporalCrossingMean
      H energyIdentity energyNontrivial
  have hMean : ∀ X Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            crossing U X Y) = crossingMean := by
    intro X Y
    dsimp [crossing, crossingMean]
    exact finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq_crossingMean
      H energyIdentity energyNontrivial X Y
  have hdecomp : ∀ X Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteUniformSlabSecondMoment left right crossing X Y =
        finiteUniformSlabSecondMomentInteraction left right crossing X Y +
          (left X) ^ 2 + (right Y) ^ 2 +
          2 * crossingMean * left X + 2 * crossingMean * right Y := by
    intro X Y
    exact finiteUniformSlabSecondMoment_eq_interaction_add_additive
      left right crossing crossingMean hMean X Y
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment]
  change
    (finiteUniformSlabSecondMoment left right crossing A B -
        finiteUniformSlabSecondMomentInteraction left right crossing A B) -
      (finiteUniformSlabSecondMoment left right crossing A B' -
        finiteUniformSlabSecondMomentInteraction left right crossing A B') =
    (finiteUniformSlabSecondMoment left right crossing A' B -
        finiteUniformSlabSecondMomentInteraction left right crossing A' B) -
      (finiteUniformSlabSecondMoment left right crossing A' B' -
        finiteUniformSlabSecondMomentInteraction left right crossing A' B')
  rw [hdecomp A B, hdecomp A B', hdecomp A' B, hdecomp A' B']
  ring

/-- Scaling the raw Package-V second moment does not change its double-centered
reduction to the scaled interaction kernel. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_scaled_doubleCentered_eq_scaledInteraction
    (H : ℕ)
    (energyIdentity energyNontrivial c : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
            c * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
              H energyIdentity energyNontrivial A B)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
            c * finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
              H energyIdentity energyNontrivial A B)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  apply
    finiteUniformAverageComplement_comp_finiteKernelOperator_congr_of_sub_right_independent
      (K := fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
        c * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial A B)
      (L := fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
        c * finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
          H energyIdentity energyNontrivial A B)
  intro A A' B B'
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_sub_interaction_sub_right_independent
      H energyIdentity energyNontrivial A A' B B'
  linear_combination c * h

/-- At the exact beta-zero normalization value, the scaled Package-V
interaction kernel is pointwise the normalized temporal crossing second moment
plus the normalized spatial rank-one kernel. -/
theorem finiteEvenFourTorusZ2ScaledOneSlabSecondMomentInteraction_eq_uniformNormalizedInteraction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
        finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
          H energyIdentity energyNontrivial A B =
      finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
        H energyIdentity energyNontrivial A B := by
  unfold finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
    finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
    finiteUniformNormalizedSpatialRankOneKernel
  rw [finiteEvenFourTorusZ2OneSlabSecondMomentInteraction_eq]
  ring

/-- Package V plus the exact beta-zero normalization value reduce the complete
normalized second-variation model to the normalized crossing-second-moment plus
spatial-rank-one interaction kernel.  The first and second derivatives of the
scalar normalization do not survive double centering. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_doubleCentered_eq_uniformNormalizedInteraction
    (H : ℕ)
    (energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
            H energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
            normalizationDerivative normalizationSecondDerivative)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  calc
    _ = finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
              finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
                H energyIdentity energyNontrivial A B)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) :=
      finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_doubleCentered_eq_scaledRaw
        H energyIdentity energyNontrivial
        (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
        normalizationDerivative normalizationSecondDerivative
    _ = finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
              finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
                H energyIdentity energyNontrivial A B)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_scaled_doubleCentered_eq_scaledInteraction
        H energyIdentity energyNontrivial
        (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
    _ = _ := by
      have hKernel :
          (fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
              finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
                H energyIdentity energyNontrivial A B) =
            finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
              H energyIdentity energyNontrivial := by
        funext A B
        exact
          finiteEvenFourTorusZ2ScaledOneSlabSecondMomentInteraction_eq_uniformNormalizedInteraction
            H energyIdentity energyNontrivial A B
      rw [hKernel]

/-- Finite kernel operators are additive in their kernels. -/
theorem finiteKernelOperator_add_kernel_toLinearMap
    {α : Type} [Fintype α]
    (K L : α → α → ℝ) :
    (finiteKernelOperator (fun x y => K x y + L x y)).toLinearMap =
      (finiteKernelOperator K).toLinearMap +
        (finiteKernelOperator L).toLinearMap := by
  apply LinearMap.ext
  intro f
  ext y
  change
    finiteKernelOperator (fun x y => K x y + L x y) f y =
      finiteKernelOperator K f y + finiteKernelOperator L f y
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply,
    finiteKernelOperator_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- The normalized Package-V interaction operator splits exactly into crossing
second moment plus spatial rank-one blocks after double centering. -/
theorem finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteraction_doubleCentered_eq_crossing_add_spatial
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap) +
        finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteUniformNormalizedSpatialRankOneKernel
              (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial X))).toLinearMap.comp
            finiteUniformAverageComplementLinearMap) := by
  have hKernel :
      finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
          H energyIdentity energyNontrivial =
        fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
          finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial A B +
            finiteUniformNormalizedSpatialRankOneKernel
              (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial X)
              A B := by
    rfl
  rw [hKernel, finiteKernelOperator_add_kernel_toLinearMap]
  apply LinearMap.ext
  intro f
  simp

/-- Conditional actual finite-Z₂ connected second-order reduction.  Any valid
second-order transfer/projector data whose beta-zero projector is uniform
averaging and whose first/second transfer variations are the Package-W/V
product-rule models has connected transfer block equal to the normalized
temporal crossing second moment alone. -/
theorem finiteEvenFourTorusZ2ConnectedTransferSecondVariation_eq_normalizedCrossing_of_models
    (H : ℕ)
    (energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative : ℝ)
    (D : FiniteSecondOrderLinearizedTransferGroundProjectorData
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
            H energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
            normalizationDerivative)).toLinearMap)
    (hTransferSecondVariation :
      D.transferSecondVariation =
        (finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
            H energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
            normalizationDerivative normalizationSecondDerivative)).toLinearMap) :
    D.connectedTransferSecondVariation =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  let Q :
      FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
        FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) :=
    finiteUniformAverageComplementLinearMap
  have hComplement : D.baseComplement = Q := by
    unfold FiniteLinearizedTransferGroundProjectorData.baseComplement
    dsimp [Q]
    unfold finiteUniformAverageComplementLinearMap
    rw [hProjector]
  have hSecond :
      D.baseComplement.comp
          (D.transferSecondVariation.comp D.baseComplement) =
        Q.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp Q) := by
    rw [hComplement, hTransferSecondVariation]
    exact
      finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_doubleCentered_eq_uniformNormalizedInteraction
        H energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative
  have hSplit :
      Q.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteractionKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp Q) =
        Q.comp
            ((finiteKernelOperator
              (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
                H energyIdentity energyNontrivial)).toLinearMap.comp Q) +
          Q.comp
            ((finiteKernelOperator
              (finiteUniformNormalizedSpatialRankOneKernel
                (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                  finiteEvenFourTorusZ2SpatialWilsonAction
                    H energyIdentity energyNontrivial X))).toLinearMap.comp Q) := by
    exact
      finiteEvenFourTorusZ2UniformNormalizedSecondMomentInteraction_doubleCentered_eq_crossing_add_spatial
        H energyIdentity energyNontrivial
  have hMixRange :
      D.baseComplement.comp D.firstVariationGroundMixing =
        D.firstVariationGroundMixing := by
    apply LinearMap.ext
    intro x
    exact D.baseComplement_firstVariationGroundMixing_apply x
  have hMixQ :
      D.baseComplement.comp D.firstVariationGroundMixing +
          D.baseComplement.comp D.firstVariationGroundMixing =
        Q.comp
          ((finiteKernelOperator
            (finiteUniformNormalizedSpatialRankOneKernel
              (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial X))).toLinearMap.comp Q) := by
    unfold FiniteSecondOrderLinearizedTransferGroundProjectorData.firstVariationGroundMixing
    rw [hComplement, hTransferVariation, hProjector]
    exact
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_groundMixing_double_eq_spatialRankOne
        H energyIdentity energyNontrivial normalizationDerivative
  have hMix :
      D.firstVariationGroundMixing + D.firstVariationGroundMixing =
        Q.comp
          ((finiteKernelOperator
            (finiteUniformNormalizedSpatialRankOneKernel
              (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial X))).toLinearMap.comp Q) := by
    calc
      D.firstVariationGroundMixing + D.firstVariationGroundMixing =
          D.baseComplement.comp D.firstVariationGroundMixing +
            D.baseComplement.comp D.firstVariationGroundMixing := by
        rw [hMixRange]
      _ = _ := hMixQ
  unfold FiniteSecondOrderLinearizedTransferGroundProjectorData.connectedTransferSecondVariation
  rw [hSecond, hSplit]
  calc
    (Q.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp Q) +
        Q.comp
          ((finiteKernelOperator
            (finiteUniformNormalizedSpatialRankOneKernel
              (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial X))).toLinearMap.comp Q)) -
        D.firstVariationGroundMixing - D.firstVariationGroundMixing =
      Q.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp Q) +
        (Q.comp
          ((finiteKernelOperator
            (finiteUniformNormalizedSpatialRankOneKernel
              (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial X))).toLinearMap.comp Q) -
          (D.firstVariationGroundMixing + D.firstVariationGroundMixing)) := by
      abel
    _ = Q.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp Q) := by
      rw [hMix]
      simp
    _ = _ := by
      rfl

/-- Conditional ground-lifted form of the same Package-W reduction:

`Q D₂_lift Q = - |C_H|⁻¹ Q M₂_cross Q`.

No differentiability of the actual operator norm or moving spectral projector
is asserted here; the theorem applies to valid second-order linearized data
satisfying the displayed actual finite-Z₂ product-rule models. -/
theorem finiteEvenFourTorusZ2GroundLiftedSecondVariation_eq_neg_normalizedCrossing_of_models
    (H : ℕ)
    (energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative : ℝ)
    (D : FiniteSecondOrderLinearizedTransferGroundProjectorData
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
            H energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
            normalizationDerivative)).toLinearMap)
    (hTransferSecondVariation :
      D.transferSecondVariation =
        (finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
            H energyIdentity energyNontrivial
            (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
            normalizationDerivative normalizationSecondDerivative)).toLinearMap) :
    D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement) =
      -finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
            H energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  rw [D.baseComplement_comp_groundLiftedSecondVariation_comp_baseComplement_eq_neg_connected]
  rw [finiteEvenFourTorusZ2ConnectedTransferSecondVariation_eq_normalizedCrossing_of_models
    H energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative
    D hProjector hTransferVariation hTransferSecondVariation]

end

end MathlibAnalytic
end MGAP4D
