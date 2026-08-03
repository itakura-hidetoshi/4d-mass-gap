import MGAP4D.MathlibAnalytic.FiniteDimensionalExtendedSpectralEnergy
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundExcitationProperties
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Ground coordinates of the actual compressed Gauss-invariant finite `Z₂`
unfixed-gauge transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundCoordinates

/-- Strictly excited coordinates of the actual compressed transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitedCoordinates

/-- Null coordinates of the actual compressed transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).nullCoordinates

/-- Synthesis of actual ground coordinates into the invariant slice Hilbert
space. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundSpectralSynthesis

/-- Synthesis of actual strictly excited coordinates. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitedSpectralSynthesis

/-- Synthesis of actual null coordinates. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeNullSpectralSynthesis
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).nullSpectralSynthesis

/-- Diagonal natural-time semigroup on the actual strictly excited sector. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSemigroup
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →L[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitedSpectralSemigroup n

/-- Complete natural-time evolution of the actual compressed transfer,
including the time-zero null sector and its disappearance at positive time. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).fullSpectralNaturalTime n

/-- Extended energy of an actual complete canonical transfer mode. -/
def finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
      H β energyIdentity energyNontrivial hβ hEnergy)) :
    ExtendedSpectralEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).extendedSpectralEnergy i

/-- Exact decomposition of every actual invariant finite-volume state into
its ground, strictly excited, and null spectral sectors. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_ground_add_excited_add_null
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) +
      finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) +
      finiteEvenFourTorusZ2UnfixedGaugeNullSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) = x :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundSynthesis_add_excitedSynthesis_add_nullSynthesis x

/-- The actual one-step transfer is exactly persistent ground plus evolved
strictly excited synthesis; null coordinates disappear. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_transfer_eq_ground_add_excited
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x =
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) +
      finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).excitedSpectralTransfer
          (finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
            H β energyIdentity energyNontrivial hβ hEnergy x)) := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).operator_eq_ground_add_excited x

/-- The kernel of the actual compressed transfer is exactly its synthesized
null sector. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_transfer_eq_zero_iff_null
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x = 0 ↔
      x = finiteEvenFourTorusZ2UnfixedGaugeNullSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).operator_eq_zero_iff_eq_nullSynthesis x

/-- Fixed vectors of the actual compressed transfer are exactly synthesized
ground vectors. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_transfer_eq_self_iff_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x = x ↔
      x = finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).operator_eq_self_iff_eq_groundSynthesis x

/-- An actual invariant state lies in the transfer range exactly when its null
coordinates vanish. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_exists_transfer_preimage_iff_nullCoordinates_eq_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (y : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (∃ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x = y) ↔
      finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
        H β energyIdentity energyNontrivial hβ hEnergy y = 0 := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).exists_operator_preimage_iff_nullCoordinates_eq_zero y

/-- Actual complete natural time starts at the identity. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ hEnergy 0 = 1 :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).fullSpectralNaturalTime_zero

/-- One unit of actual complete natural time is the original compressed
transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ hEnergy 1 =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy).fullSpectralNaturalTime_one

/-- Actual complete natural time is additive under composition. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_add
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (m n : ℕ) :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
      (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ hEnergy m).comp
      (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ hEnergy n) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).fullSpectralNaturalTime_add m n

/-- Every positive actual natural time has zero null coordinates. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_nullCoordinates_fullSpectralNaturalTime_eq_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (hn : 0 < n)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeNullCoordinates
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          H β energyIdentity energyNontrivial hβ hEnergy n x) = 0 :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).nullCoordinates_fullSpectralNaturalTime_eq_zero n hn x

/-- At positive actual natural time the state is exactly ground plus evolved
strictly excited synthesis. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_fullSpectralNaturalTime_eq_ground_add_excited
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (hn : 0 < n)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ hEnergy n x =
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) +
      finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy n
          (finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
            H β energyIdentity energyNontrivial hβ hEnergy x)) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).fullSpectralNaturalTime_eq_ground_add_excited n hn x

/-- Actual ground modes have finite extended energy zero. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
        H β energyIdentity energyNontrivial hβ hEnergy i.1 =
      ExtendedSpectralEnergy.finite 0 :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).extendedSpectralEnergy_ground i

/-- Actual strictly excited modes have finite strictly positive support
energy. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_excited
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
        H β energyIdentity energyNontrivial hβ hEnergy i.1 =
      ExtendedSpectralEnergy.finite
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
          H β energyIdentity energyNontrivial hβ hEnergy i.toPositive) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).extendedSpectralEnergy_excited i

/-- The finite extended energy of every actual strictly excited mode is
strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_excited_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
      H β energyIdentity energyNontrivial hβ hEnergy i.toPositive :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).extendedSpectralEnergy_excited_pos i

/-- Actual null modes have infinite extended energy. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_null
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
        H β energyIdentity energyNontrivial hβ hEnergy i.1 =
      ExtendedSpectralEnergy.infinite :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).extendedSpectralEnergy_null i

end

end MathlibAnalytic
end MGAP4D
