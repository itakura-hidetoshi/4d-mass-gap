import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepMultiplicityNormalizedConfigurationFiber
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Actual configuration-fibre averages obey the exact direct-versus-successive
two-step tower law. -/
theorem finiteEvenFourTorusZ2SliceConfigurationMultiplicityNormalizedFiberAverage_twoStep
    (H : ℕ)
    (w : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)) → ℝ)
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteSurjectiveGroupHomFiberAverage
        (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H) w b =
      finiteSurjectiveGroupHomFiberAverage
        (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
        (finiteSurjectiveGroupHomFiberAverage
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
            (finiteEvenFourTorusDoubleRefinement H)) w) b := by
  exact finiteSurjectiveGroupHomFiberAverage_comp
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H) w b

/-- Package-L receipt: canonical raw Wilson transfer comparison fails at
`β = 0`, while exact multiplicity-normalized fibre averaging restores the
configurationwise one-step and direct two-step balances and itself composes
functorially. -/
structure Z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedFiberRenormalizationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepRawResidualNonzero :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0
  twoStepRawResidualNonzero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0
  oneStepNormalizedOrbitBalance :
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepNormalizedOrbitBalance :
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  oneStepNormalizedConfigurationBalance :
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepNormalizedConfigurationBalance :
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepMultiplicityFactorization :
    Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker =
      Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
            (finiteEvenFourTorusDoubleRefinement H)).ker *
        Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker
  fiberAverageTower :
    ∀ (w : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) → ℝ)
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteSurjectiveGroupHomFiberAverage
          (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H) w b =
        finiteSurjectiveGroupHomFiberAverage
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
          (finiteSurjectiveGroupHomFiberAverage
            (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
              (finiteEvenFourTorusDoubleRefinement H)) w) b

/-- Construct the full Package-L receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedFiberRenormalizationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedFiberRenormalizationPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStepRawResidualNonzero :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepRawResidualNonzero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy
  oneStepNormalizedOrbitBalance :=
    finiteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepNormalizedOrbitBalance :=
    finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy
  oneStepNormalizedConfigurationBalance :=
    finiteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepNormalizedConfigurationBalance :=
    finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepMultiplicityFactorization :=
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_card_ker_factorization H
  fiberAverageTower :=
    finiteEvenFourTorusZ2SliceConfigurationMultiplicityNormalizedFiberAverage_twoStep H

end

end MathlibAnalytic
end MGAP4D
