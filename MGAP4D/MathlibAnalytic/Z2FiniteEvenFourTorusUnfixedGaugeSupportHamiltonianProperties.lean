import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeSupportHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- The actual positive-support Hamiltonian is symmetric. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralHamiltonian_isSymmetric

/-- The actual positive-support Hamiltonian is positive in quadratic form. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
        H β energyIdentity energyNontrivial hβ hEnergy x) x :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralHamiltonian_quadratic_nonneg x

/-- The actual positive-support transfer is symmetric. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralTransfer_isSymmetric

/-- The actual positive-support transfer is positive in quadratic form. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x) x :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralTransfer_quadratic_nonneg x

/-- Actual positive-support synthesis is injective. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis_injective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralSynthesis_injective

/-- Each actual support coordinate evolves with the exact Hamiltonian weight
`exp(-E)^n`. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_supportSemigroup_hamiltonian_weight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy)
    (i : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenbasis
        H β energyIdentity energyNontrivial hβ hEnergy
        |>.repr
          (((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy) ^ n)
            (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
              H β energyIdentity energyNontrivial hβ hEnergy x)) i.1 =
      (Real.exp
        (-finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
          H β energyIdentity energyNontrivial hβ hEnergy i)) ^ n * x i :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).operator_pow_positiveSpectralSynthesis_hamiltonian_weight n x i

end

end MathlibAnalytic
end MGAP4D
