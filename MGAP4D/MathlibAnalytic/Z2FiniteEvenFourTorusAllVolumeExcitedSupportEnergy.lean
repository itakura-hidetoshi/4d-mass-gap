import MGAP4D.MathlibAnalytic.FiniteDimensionalInjectiveNonidentityExcitedSupport
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingWitnessMinor
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusAllVolumeGaugeOrbitWitness
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeSupportHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- At every finite side parameter, strict physical coupling produces a genuine
strictly excited eigenvalue of the actual Gauss-invariant unfixed-gauge
one-slab transfer.  No small-coupling restriction is needed here: strict
coupling gives injectivity, while the all-volume orbit witness proves that the
transfer is not the identity. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict_allVolume
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  have hinj : Function.Injective D.operator := by
    change Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    exact
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_injective_strict
        H β energyIdentity energyNontrivial hβ hEnergy
  have hne : D.operator ≠ 1 := by
    change
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 1
    exact
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_allVolume_ne_identity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  exact D.nonempty_excitedSpectralIndex_of_operator_injective_of_ne_one hinj hne

/-- The corresponding actual support Hamiltonian contains a strictly positive
energy at every finite volume and every strict coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_exists_positiveEnergy_strict_allVolume
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le,
      0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive := by
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let i : D.ExcitedSpectralIndex := Classical.choice
    (finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict_allVolume
      H β energyIdentity energyNontrivial hβ hEnergy)
  refine ⟨i, ?_⟩
  simpa [D, finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy] using
    D.excitedSpectralEnergy_pos i

/-- The actual Gauss-invariant positive-support Hamiltonian is nonzero at every
finite volume in the strict-coupling regime. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_ne_zero_strict_allVolume
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
      H β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 0 := by
  let D :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  have hex : Nonempty D.ExcitedSpectralIndex :=
    finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict_allVolume
      H β energyIdentity energyNontrivial hβ hEnergy
  simpa [D, finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian] using
    D.positiveSpectralHamiltonian_ne_zero_of_nonempty_excitedSpectralIndex hex

/-- Strict coupling simultaneously removes the null sector and produces a
strictly excited positive-energy sector at every finite side parameter. -/
structure Z2FiniteEvenFourTorusAllVolumeExcitedSupportEnergyPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  transferInjective :
    Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  transferNonidentity :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 1
  nullSectorEmpty :
    ¬ Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  excitedSectorNonempty :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  positiveEnergy :
    ∃ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le,
      0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive
  supportHamiltonianNonzero :
    finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
      H β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 0

/-- Construct the all-volume strict-coupling Package-AB receipt. -/
noncomputable def z2FiniteEvenFourTorusAllVolumeExcitedSupportEnergyPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusAllVolumeExcitedSupportEnergyPackage
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { transferInjective :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_injective_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    transferNonidentity :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_allVolume_ne_identity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    nullSectorEmpty :=
      finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    excitedSectorNonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict_allVolume
        H β energyIdentity energyNontrivial hβ hEnergy
    positiveEnergy :=
      finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_exists_positiveEnergy_strict_allVolume
        H β energyIdentity energyNontrivial hβ hEnergy
    supportHamiltonianNonzero :=
      finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian_ne_zero_strict_allVolume
        H β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
