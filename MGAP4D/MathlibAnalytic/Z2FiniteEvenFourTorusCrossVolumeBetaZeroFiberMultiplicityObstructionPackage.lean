import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Audit-visible one-step Package-K receipt: orbit-mass cancellation,
nontrivial configuration coarse kernel, and genuine `β = 0` raw-transfer
cross-volume obstruction. -/
structure Z2FiniteEvenFourTorusCrossVolumeOneStepBetaZeroFiberMultiplicityObstructionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  cardinalityScale : ℝ
  cardinalityScale_eq : cardinalityScale =
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
  cardinalityScale_pos : 0 < cardinalityScale
  coarseKernelCardinality_gt_one :
    1 < Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker
  boltzmannBalanceFails :
    ¬ FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  rawResidual_ne_zero :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0

/-- Construct the one-step Package-K receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOneStepBetaZeroFiberMultiplicityObstructionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeOneStepBetaZeroFiberMultiplicityObstructionPackage
      H energyIdentity energyNontrivial hEnergy where
  cardinalityScale :=
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
  cardinalityScale_eq := rfl
  cardinalityScale_pos :=
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_pos H
  coarseKernelCardinality_gt_one :=
    finiteEvenFourTorusZ2SliceConfigurationCoarseHom_card_ker_gt_one H
  boltzmannBalanceFails :=
    finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy
  rawResidual_ne_zero :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy

/-- Audit-visible direct two-step Package-K receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstructionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  cardinalityScale : ℝ
  cardinalityScale_eq : cardinalityScale =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H
  cardinalityScale_pos : 0 < cardinalityScale
  directKernelCardinality_gt_one :
    1 < Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker
  boltzmannBalanceFails :
    ¬ FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  rawResidual_ne_zero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0

/-- Construct the direct two-step Package-K receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstructionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstructionPackage
      H energyIdentity energyNontrivial hEnergy where
  cardinalityScale :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H
  cardinalityScale_eq := rfl
  cardinalityScale_pos :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale_pos H
  directKernelCardinality_gt_one :=
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_card_ker_gt_one H
  boltzmannBalanceFails :=
    finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy
  rawResidual_ne_zero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy

/-- Full one-step/direct-two-step Package-K obstruction bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeBetaZeroFiberMultiplicityObstructionFullPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep :
    Z2FiniteEvenFourTorusCrossVolumeOneStepBetaZeroFiberMultiplicityObstructionPackage
      H energyIdentity energyNontrivial hEnergy
  twoStep :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstructionPackage
      H energyIdentity energyNontrivial hEnergy

/-- Construct the full Package-K obstruction bundle. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeBetaZeroFiberMultiplicityObstructionFullPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeBetaZeroFiberMultiplicityObstructionFullPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStep :=
    z2FiniteEvenFourTorusCrossVolumeOneStepBetaZeroFiberMultiplicityObstructionPackage
      H energyIdentity energyNontrivial hEnergy
  twoStep :=
    z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstructionPackage
      H energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D
