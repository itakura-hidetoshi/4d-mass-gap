import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossingSecondMomentOperatorWitness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Audit-visible Package-X receipt for the minimal side-two finite Z₂ temporal
crossing second-moment witness.

The receipt records the exact mixed second-moment defect, raw and normalized
complement-block nontriviality, and the conditional connected/ground-lifted
second-order consequences under Package W's actual finite-Z₂ product-rule
model hypotheses. -/
structure Z2FiniteEvenFourTorusCrossingSecondMomentWitnessPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  exactMixedDifference :
    finiteKernelMixedCrossDifference
      (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation =
        2 * (energyNontrivial - energyIdentity) ^ 2
  rawDoubleCenteredNonzero :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
            0 energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) ≠ 0
  normalizedDoubleCenteredNonzero :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
            0 energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) ≠ 0
  connectedNonzero :
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
      D.connectedTransferSecondVariation ≠ 0
  groundLiftedNonzero :
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
      D.baseComplement.comp
          (D.groundLiftedSecondVariation.comp D.baseComplement) ≠ 0

/-- Construct the Package-X receipt from the explicit side-two witness and the
Package-W connected second-order reduction. -/
noncomputable def z2FiniteEvenFourTorusCrossingSecondMomentWitnessPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusCrossingSecondMomentWitnessPackage
      energyIdentity energyNontrivial hEnergy where
  exactMixedDifference :=
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero
      energyIdentity energyNontrivial
  rawDoubleCenteredNonzero :=
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment_doubleCentered_ne_zero_zero
      energyIdentity energyNontrivial hEnergy
  normalizedDoubleCenteredNonzero :=
    finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMoment_doubleCentered_ne_zero_zero
      energyIdentity energyNontrivial hEnergy
  connectedNonzero :=
    fun normalizationDerivative normalizationSecondDerivative D hProjector
        hTransferVariation hTransferSecondVariation =>
      finiteEvenFourTorusZ2ConnectedTransferSecondVariation_ne_zero_zero_of_models
        energyIdentity energyNontrivial normalizationDerivative
        normalizationSecondDerivative hEnergy D hProjector hTransferVariation
        hTransferSecondVariation
  groundLiftedNonzero :=
    fun normalizationDerivative normalizationSecondDerivative D hProjector
        hTransferVariation hTransferSecondVariation =>
      finiteEvenFourTorusZ2GroundLiftedSecondVariation_ne_zero_zero_of_models
        energyIdentity energyNontrivial normalizationDerivative
        normalizationSecondDerivative hEnergy D hProjector hTransferVariation
        hTransferSecondVariation

end

end MathlibAnalytic
end MGAP4D
