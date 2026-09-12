import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCrossingReduction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Audit-visible Package-W receipt.

The package records both the exact finite-Z₂ first-order additive model and the
second-order connected reduction.  The latter is deliberately conditional on
valid second-order linearized transfer/projector data matching the finite-Z₂
product-rule models; no differentiability of the actual operator norm or moving
spectral projector is asserted here. -/
structure Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    extends
      Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellationPackage
        H energyIdentity energyNontrivial where
  connectedCrossingReduction :
    ∀ normalizationDerivative normalizationSecondDerivative : ℝ,
      ∀ D : FiniteSecondOrderLinearizedTransferGroundProjectorData
        (FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)),
      D.baseProjector =
          (finiteUniformAverageProjectorLinearMap :
            FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
              FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)) →
      D.transferVariation =
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
              H energyIdentity energyNontrivial
              (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
              normalizationDerivative)).toLinearMap →
      D.transferSecondVariation =
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
              H energyIdentity energyNontrivial
              (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
              normalizationDerivative normalizationSecondDerivative)).toLinearMap →
      D.connectedTransferSecondVariation =
        finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap)
  groundLiftedCrossingReduction :
    ∀ normalizationDerivative normalizationSecondDerivative : ℝ,
      ∀ D : FiniteSecondOrderLinearizedTransferGroundProjectorData
        (FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)),
      D.baseProjector =
          (finiteUniformAverageProjectorLinearMap :
            FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
              FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)) →
      D.transferVariation =
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
              H energyIdentity energyNontrivial
              (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
              normalizationDerivative)).toLinearMap →
      D.transferSecondVariation =
          (finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
              H energyIdentity energyNontrivial
              (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
              normalizationDerivative normalizationSecondDerivative)).toLinearMap →
      D.baseComplement.comp
          (D.groundLiftedSecondVariation.comp D.baseComplement) =
        -finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
              H energyIdentity energyNontrivial)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap)

/-- Construct the Package-W receipt from the proved finite-Z₂ first-order and
connected second-order reductions. -/
noncomputable def z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderPackage
      H energyIdentity energyNontrivial where
  toZ2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellationPackage :=
    z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellationPackage
      H energyIdentity energyNontrivial
  connectedCrossingReduction :=
    fun normalizationDerivative normalizationSecondDerivative D hProjector
        hTransferVariation hTransferSecondVariation =>
      finiteEvenFourTorusZ2ConnectedTransferSecondVariation_eq_normalizedCrossing_of_models
        H energyIdentity energyNontrivial normalizationDerivative
        normalizationSecondDerivative D hProjector hTransferVariation
        hTransferSecondVariation
  groundLiftedCrossingReduction :=
    fun normalizationDerivative normalizationSecondDerivative D hProjector
        hTransferVariation hTransferSecondVariation =>
      finiteEvenFourTorusZ2GroundLiftedSecondVariation_eq_neg_normalizedCrossing_of_models
        H energyIdentity energyNontrivial normalizationDerivative
        normalizationSecondDerivative D hProjector hTransferVariation
        hTransferSecondVariation

end

end MathlibAnalytic
end MGAP4D
