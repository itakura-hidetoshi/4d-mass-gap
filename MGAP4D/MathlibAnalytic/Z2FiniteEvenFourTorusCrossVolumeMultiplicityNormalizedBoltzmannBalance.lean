import MGAP4D.MathlibAnalytic.FiniteSurjectiveGroupHomFiberAverage
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroFiberMultiplicityObstructionPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- One-step fine Boltzmann orbit-fibre coefficient with the exact configuration
fibre multiplicity divided out. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) : ℝ :=
  (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ)⁻¹ *
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy A q

/-- Multiplicity-normalized one-step Boltzmann compatibility.  This is a new
renormalized comparison, not a claim that the original raw transfer
intertwines. -/
def FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
    finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q

/-- At `β = 0`, exact division by the configuration-fibre multiplicity removes
the Package-K obstruction and gives exact one-step balance. -/
theorem finiteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  intro A q
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient_beta_zero,
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient_beta_zero]
  have hker :
      (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) ≠ 0 :=
    finiteSurjectiveGroupHom_card_ker_real_ne_zero
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
  field_simp [hker]

/-- Package K and the corrected comparison sharply separate at `β = 0`: the
original balance is false while the multiplicity-normalized balance is true. -/
theorem finiteEvenFourTorusZ2OneStepRawFalse_normalizedTrue_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (¬ FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy) ∧
      FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy :=
  ⟨finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy,
    finiteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy⟩

/-- Direct finest-to-coarsest Boltzmann coefficient with the exact composed
configuration-fibre multiplicity divided out. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) : ℝ :=
  (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ)⁻¹ *
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy A q

/-- Direct two-step multiplicity-normalized Boltzmann balance. -/
def FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
    finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q

/-- The direct two-step configuration-fibre multiplicity factors exactly into
the two successive one-step kernel cardinalities. -/
theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_card_ker_factorization
    (H : ℕ) :
    Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker =
      Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
            (finiteEvenFourTorusDoubleRefinement H)).ker *
        Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker := by
  exact finiteSurjectiveGroupHom_card_ker_comp
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H)

/-- At `β = 0`, multiplicity normalization also removes the direct two-step
obstruction exactly. -/
theorem finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  intro A q
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient_beta_zero,
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient_beta_zero]
  have hker :
      (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) ≠ 0 :=
    finiteSurjectiveGroupHom_card_ker_real_ne_zero
      (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H)
  field_simp [hker]

/-- The same sharp raw-versus-normalized separation holds for direct two-step
refinement at `β = 0`. -/
theorem finiteEvenFourTorusZ2TwoStepRawFalse_normalizedTrue_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (¬ FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy) ∧
      FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy :=
  ⟨finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy,
    finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy⟩

/-- Audit-visible one-step/direct-two-step multiplicity-normalized package. -/
structure Z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedBoltzmannPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepRawFails :
    ¬ FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  oneStepNormalizedHolds :
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepRawFails :
    ¬ FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepNormalizedHolds :
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  twoStepMultiplicityFactorization :
    Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker =
      Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
            (finiteEvenFourTorusDoubleRefinement H)).ker *
        Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker

/-- Construct the β=0 multiplicity-normalized Package-L core. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedBoltzmannPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedBoltzmannPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStepRawFails :=
    finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy
  oneStepNormalizedHolds :=
    finiteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepRawFails :=
    finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_false
      H energyIdentity energyNontrivial hEnergy
  twoStepNormalizedHolds :=
    finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepMultiplicityFactorization :=
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_card_ker_factorization H

end

end MathlibAnalytic
end MGAP4D
