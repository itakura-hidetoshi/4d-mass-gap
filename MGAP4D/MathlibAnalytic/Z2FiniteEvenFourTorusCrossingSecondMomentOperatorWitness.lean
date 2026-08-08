import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossingSecondMomentEnergyWitness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit side-two mixed-difference witness certifies that the raw
temporal crossing second-moment kernel has a nonzero uniform-average
complement-to-complement block. -/
theorem finiteEvenFourTorusZ2TemporalCrossingSecondMoment_doubleCentered_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
            0 energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) ≠ 0 := by
  exact
    finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_ne_zero_of_mixedCrossDifference_ne_zero
      (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      (finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero_ne_zero
        energyIdentity energyNontrivial hEnergy)

/-- Exact mixed difference after inserting Package W's beta-zero boundary-cardinality
normalization. -/
theorem finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel_mixedDifference_witness_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteKernelMixedCrossDifference
      (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation =
        (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹ *
          (2 * (energyNontrivial - energyIdentity) ^ 2) := by
  have h :=
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero
      energyIdentity energyNontrivial
  unfold finiteKernelMixedCrossDifference
    finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
  unfold finiteKernelMixedCrossDifference at h
  linear_combination
    (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹ * h

/-- The normalized temporal crossing second-moment mixed witness is nonzero
under the strict physical energy ordering. -/
theorem finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel_mixedDifference_witness_zero_ne_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteKernelMixedCrossDifference
      (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation ≠ 0 := by
  rw [finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel_mixedDifference_witness_zero]
  have hcard :
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) ≠ 0)
  have hgap : energyNontrivial - energyIdentity ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hEnergy)
  exact mul_ne_zero (inv_ne_zero hcard)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hgap))

/-- Therefore Package W's normalized temporal crossing second-moment operator
has a nonzero uniform-average complement block already at `H=0`. -/
theorem finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMoment_doubleCentered_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
            0 energyIdentity energyNontrivial)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) ≠ 0 := by
  exact
    finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_ne_zero_of_mixedCrossDifference_ne_zero
      (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMomentKernel_mixedDifference_witness_zero_ne_zero
        energyIdentity energyNontrivial hEnergy)

/-- Conditional finite-Z₂ connected second-order obstruction.  Any valid
second-order linearized transfer/projector data matching Package W's actual
finite-Z₂ product-rule models has nonzero connected transfer second variation at
`H=0` under strict physical energy ordering. -/
theorem finiteEvenFourTorusZ2ConnectedTransferSecondVariation_ne_zero_zero_of_models
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
            normalizationDerivative normalizationSecondDerivative)).toLinearMap) :
    D.connectedTransferSecondVariation ≠ 0 := by
  rw [finiteEvenFourTorusZ2ConnectedTransferSecondVariation_eq_normalizedCrossing_of_models
    0 energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative
    D hProjector hTransferVariation hTransferSecondVariation]
  exact
    finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMoment_doubleCentered_ne_zero_zero
      energyIdentity energyNontrivial hEnergy

/-- Conditional finite-Z₂ ground-lifted second-order obstruction.  Under the
same Package-W model hypotheses, the complemented second variation of the
ground-lifted defect is nonzero at `H=0`. -/
theorem finiteEvenFourTorusZ2GroundLiftedSecondVariation_ne_zero_zero_of_models
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
            normalizationDerivative normalizationSecondDerivative)).toLinearMap) :
    D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement) ≠ 0 := by
  rw [finiteEvenFourTorusZ2GroundLiftedSecondVariation_eq_neg_normalizedCrossing_of_models
    0 energyIdentity energyNontrivial normalizationDerivative normalizationSecondDerivative
    D hProjector hTransferVariation hTransferSecondVariation]
  exact neg_ne_zero.mpr
    (finiteEvenFourTorusZ2UniformNormalizedTemporalCrossingSecondMoment_doubleCentered_ne_zero_zero
      energyIdentity energyNontrivial hEnergy)

end

end MathlibAnalytic
end MGAP4D
