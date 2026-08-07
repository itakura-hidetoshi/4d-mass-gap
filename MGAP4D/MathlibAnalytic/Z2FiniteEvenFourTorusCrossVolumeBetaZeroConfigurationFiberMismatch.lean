import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberTemporalLinkBoltzmann
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroFiberMultiplicityObstructionPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Package K's β=0 obstruction, expressed in the explicit one-step temporal-
link configuration-fibre coordinates of the complementary reduction package. -/
theorem finiteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance_beta_zero_false
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ¬ FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  intro hBalance
  have hOrbit :=
    (finiteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance_iff_boltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).1 hBalance
  exact finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_false
    H energyIdentity energyNontrivial hEnergy hOrbit

/-- Hence at β=0 there is an actual fine evaluation configuration and an
individual coarse configuration for which the exact one-step fibre-pushed raw
kernel coefficient disagrees with the coarse comparison coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStep_exists_configurationFiberKernelMismatch_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b ≠
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b := by
  classical
  have hResidual :
      finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0 :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy
  have hNotAll :
      ¬ ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b := by
    intro hAll
    apply hResidual
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).2 hAll
  push_neg at hNotAll
  exact hNotAll

/-- Direct two-step Package K obstruction in the explicit temporal-link
configuration-fibre presentation. -/
theorem finiteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance_beta_zero_false
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ¬ FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  intro hBalance
  have hOrbit :=
    (finiteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance_iff_boltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).1 hBalance
  exact finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_false
    H energyIdentity energyNontrivial hEnergy hOrbit

/-- At β=0 the direct finest-to-coarsest comparison also has an individual
coarsest configuration carrying a genuine configuration-fibre mismatch. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStep_exists_configurationFiberKernelMismatch_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b ≠
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b := by
  classical
  have hResidual :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0 :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy
  have hNotAll :
      ¬ ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b := by
    intro hAll
    apply hResidual
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).2 hAll
  push_neg at hNotAll
  exact hNotAll

/-- Audit-visible Package L: the exact configuration-fibre / temporal-link
presentation survives the β=0 negative result and exposes actual individual
coarse-configuration mismatch witnesses at one and two refinement steps. -/
structure Z2FiniteEvenFourTorusCrossVolumeBetaZeroConfigurationFiberMismatchPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepTemporalLinkBalanceFails :
    ¬ FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  oneStepMismatch :
    ∃ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b ≠
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b
  twoStepTemporalLinkBalanceFails :
    ¬ FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepMismatch :
    ∃ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b ≠
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A b

/-- Construct the complete Package-L mismatch receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeBetaZeroConfigurationFiberMismatchPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeBetaZeroConfigurationFiberMismatchPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStepTemporalLinkBalanceFails :=
    finiteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy
  oneStepMismatch :=
    finiteEvenFourTorusZ2GaugeInvariantOneStep_exists_configurationFiberKernelMismatch_beta_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepTemporalLinkBalanceFails :=
    finiteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy
  twoStepMismatch :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStep_exists_configurationFiberKernelMismatch_beta_zero
      H energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D
