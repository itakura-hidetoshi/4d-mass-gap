import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeFullSpectralDecomposition
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundExcitationCompletePackage

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Complete side-two full-space spectral package for the actual finite `Z₂`
Gauss-invariant unfixed-gauge one-slab transfer.

The package contains the previous positive-support ground/excitation package
and extends it to the entire invariant Hilbert space by separating the null
sector, characterizing kernel/fixed/range spaces, constructing complete
natural time, and classifying zero transfer modes as infinite extended
energy. -/
structure Z2UnfixedGaugeFullSpectralCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  supportPackage :
    Z2UnfixedGaugeGroundExcitationCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy
  full_decomposition :
    ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x) +
        finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x) +
        finiteEvenFourTorusZ2UnfixedGaugeNullSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x) = x
  kernel_characterization :
    ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy x = 0 ↔
        x = finiteEvenFourTorusZ2UnfixedGaugeNullSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x)
  fixed_characterization :
    ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy x = x ↔
        x = finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x)
  range_characterization :
    ∀ y : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
      (∃ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy x = y) ↔
        finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
          0 β energyIdentity energyNontrivial hβ hEnergy y = 0
  naturalTime_zero :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        0 β energyIdentity energyNontrivial hβ hEnergy 0 = 1
  naturalTime_one :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        0 β energyIdentity energyNontrivial hβ hEnergy 1 =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy
  naturalTime_add :
    ∀ m n : ℕ,
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          0 β energyIdentity energyNontrivial hβ hEnergy (m + n) =
        (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          0 β energyIdentity energyNontrivial hβ hEnergy m).comp
        (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          0 β energyIdentity energyNontrivial hβ hEnergy n)
  positiveTime_nullCoordinates_zero :
    ∀ (n : ℕ), 0 < n →
      ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
        finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy
            (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
              0 β energyIdentity energyNontrivial hβ hEnergy n x) = 0
  positiveTime_ground_add_excited :
    ∀ (n : ℕ), 0 < n →
      ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0,
        finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
            0 β energyIdentity energyNontrivial hβ hEnergy n x =
          finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
            0 β energyIdentity energyNontrivial hβ hEnergy
            (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
              0 β energyIdentity energyNontrivial hβ hEnergy x) +
          finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
            0 β energyIdentity energyNontrivial hβ hEnergy
            (finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSemigroup
              0 β energyIdentity energyNontrivial hβ hEnergy n
              (finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
                0 β energyIdentity energyNontrivial hβ hEnergy x))
  ground_extendedEnergy_zero :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
      0 β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
          0 β energyIdentity energyNontrivial hβ hEnergy i.1 =
        ExtendedSpectralEnergy.finite 0
  excited_extendedEnergy_finite :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      0 β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
          0 β energyIdentity energyNontrivial hβ hEnergy i.1 =
        ExtendedSpectralEnergy.finite
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
            0 β energyIdentity energyNontrivial hβ hEnergy i.toPositive)
  excited_extendedEnergy_pos :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      0 β energyIdentity energyNontrivial hβ hEnergy,
      0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        0 β energyIdentity energyNontrivial hβ hEnergy i.toPositive
  null_extendedEnergy_infinite :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
      0 β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
          0 β energyIdentity energyNontrivial hβ hEnergy i.1 =
        ExtendedSpectralEnergy.infinite

/-- The actual side-two compressed transfer supplies the complete full-space
spectral package. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeFullSpectralCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2UnfixedGaugeFullSpectralCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { supportPackage :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundExcitationCompletePackage
        β energyIdentity energyNontrivial hβ hEnergy
    full_decomposition :=
      finiteEvenFourTorusZ2UnfixedGauge_ground_add_excited_add_null
        0 β energyIdentity energyNontrivial hβ hEnergy
    kernel_characterization :=
      finiteEvenFourTorusZ2UnfixedGauge_transfer_eq_zero_iff_null
        0 β energyIdentity energyNontrivial hβ hEnergy
    fixed_characterization :=
      finiteEvenFourTorusZ2UnfixedGauge_transfer_eq_self_iff_ground
        0 β energyIdentity energyNontrivial hβ hEnergy
    range_characterization :=
      finiteEvenFourTorusZ2UnfixedGauge_exists_transfer_preimage_iff_nullCoordinates_eq_zero
        0 β energyIdentity energyNontrivial hβ hEnergy
    naturalTime_zero :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_zero
        0 β energyIdentity energyNontrivial hβ hEnergy
    naturalTime_one :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_one
        0 β energyIdentity energyNontrivial hβ hEnergy
    naturalTime_add :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_add
        0 β energyIdentity energyNontrivial hβ hEnergy
    positiveTime_nullCoordinates_zero :=
      finiteEvenFourTorusZ2UnfixedGauge_nullCoordinates_fullSpectralNaturalTime_eq_zero
        0 β energyIdentity energyNontrivial hβ hEnergy
    positiveTime_ground_add_excited :=
      finiteEvenFourTorusZ2UnfixedGauge_fullSpectralNaturalTime_eq_ground_add_excited
        0 β energyIdentity energyNontrivial hβ hEnergy
    ground_extendedEnergy_zero :=
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_ground
        0 β energyIdentity energyNontrivial hβ hEnergy
    excited_extendedEnergy_finite :=
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_excited
        0 β energyIdentity energyNontrivial hβ hEnergy
    excited_extendedEnergy_pos :=
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_excited_pos
        0 β energyIdentity energyNontrivial hβ hEnergy
    null_extendedEnergy_infinite :=
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_null
        0 β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
