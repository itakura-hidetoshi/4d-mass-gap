import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeSupportHamiltonianProperties

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Complete side-two finite `Z₂` unfixed-gauge spectral-support Hamiltonian
package.  Every field is an analytic theorem about the actual transfer; no
full-space logarithm or spectral-gap field is included. -/
structure Z2UnfixedGaugeSupportHamiltonianCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  eigenvalue_mem_unitInterval :
    ∀ i : Fin
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
        0 β energyIdentity energyNontrivial hβ hEnergy),
      finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue
          0 β energyIdentity energyNontrivial hβ hEnergy i ∈
        Set.Icc (0 : ℝ) 1
  positiveSupport_nonempty :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
        0 β energyIdentity energyNontrivial hβ hEnergy)
  supportEnergy_nonneg :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
      0 β energyIdentity energyNontrivial hβ hEnergy,
      0 ≤ finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        0 β energyIdentity energyNontrivial hβ hEnergy i
  exp_neg_supportEnergy :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
      0 β energyIdentity energyNontrivial hβ hEnergy,
      Real.exp
          (-finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
            0 β energyIdentity energyNontrivial hβ hEnergy i) =
        finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue
          0 β energyIdentity energyNontrivial hβ hEnergy i.1
  supportHamiltonian_symmetric :
    (finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
      0 β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric
  supportHamiltonian_positive :
    ∀ x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      0 β energyIdentity energyNontrivial hβ hEnergy,
      0 ≤ inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
          0 β energyIdentity energyNontrivial hβ hEnergy x) x
  supportTransfer_symmetric :
    (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
      0 β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric
  supportTransfer_positive :
    ∀ x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      0 β energyIdentity energyNontrivial hβ hEnergy,
      0 ≤ inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy x) x
  supportSemigroup_add :
    ∀ m n : ℕ,
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
          0 β energyIdentity energyNontrivial hβ hEnergy (m + n) =
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
          0 β energyIdentity energyNontrivial hβ hEnergy m).comp
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
          0 β energyIdentity energyNontrivial hβ hEnergy n)
  synthesis_injective :
    Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
        0 β energyIdentity energyNontrivial hβ hEnergy)
  transfer_intertwining :
    ∀ x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      0 β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
            0 β energyIdentity energyNontrivial hβ hEnergy x) =
        finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
            0 β energyIdentity energyNontrivial hβ hEnergy x)
  semigroup_intertwining :
    ∀ (n : ℕ)
      (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        0 β energyIdentity energyNontrivial hβ hEnergy),
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy) ^ n)
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
            0 β energyIdentity energyNontrivial hβ hEnergy x) =
        finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
            0 β energyIdentity energyNontrivial hβ hEnergy n x)

/-- The actual side-two transfer supplies the complete nonzero spectral-support
Hamiltonian package. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonianCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2UnfixedGaugeSupportHamiltonianCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { eigenvalue_mem_unitInterval :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue_mem_unitInterval
        0 β energyIdentity energyNontrivial hβ hEnergy
    positiveSupport_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex_nonempty
        β energyIdentity energyNontrivial hβ hEnergy
    supportEnergy_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy_nonneg
        0 β energyIdentity energyNontrivial hβ hEnergy
    exp_neg_supportEnergy :=
      finiteEvenFourTorusZ2UnfixedGauge_exp_neg_supportEnergy
        0 β energyIdentity energyNontrivial hβ hEnergy
    supportHamiltonian_symmetric :=
      finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_isSymmetric
        0 β energyIdentity energyNontrivial hβ hEnergy
    supportHamiltonian_positive :=
      finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_quadratic_nonneg
        0 β energyIdentity energyNontrivial hβ hEnergy
    supportTransfer_symmetric :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer_isSymmetric
        0 β energyIdentity energyNontrivial hβ hEnergy
    supportTransfer_positive :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer_quadratic_nonneg
        0 β energyIdentity energyNontrivial hβ hEnergy
    supportSemigroup_add :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup_add
        0 β energyIdentity energyNontrivial hβ hEnergy
    synthesis_injective :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis_injective
        0 β energyIdentity energyNontrivial hβ hEnergy
    transfer_intertwining :=
      finiteEvenFourTorusZ2UnfixedGauge_supportTransfer_intertwining
        0 β energyIdentity energyNontrivial hβ hEnergy
    semigroup_intertwining :=
      finiteEvenFourTorusZ2UnfixedGauge_supportSemigroup_intertwining
        0 β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
