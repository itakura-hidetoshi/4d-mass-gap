import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundSpectrum
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabNontriviality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Ground-sector Euclidean Hilbert space of the actual compressed transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralSpace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralSpace

/-- Strictly excited Euclidean Hilbert space of the actual compressed transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).ExcitedSpectralSpace

/-- Null-sector Euclidean Hilbert space of the actual compressed transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralSpace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).NullSpectralSpace

/-- Extend actual ground coordinates inside the positive spectral support. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundPositiveExtension
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundPositiveExtension

/-- Extend actual excited coordinates inside the positive spectral support. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeExcitedPositiveExtension
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitedPositiveExtension

/-- Restrict actual positive-support coordinates to the ground sector. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugePositiveGroundCoordinates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveGroundCoordinates

/-- Restrict actual positive-support coordinates to the excited sector. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugePositiveExcitedCoordinates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveExcitedCoordinates

/-- Exact actual decomposition of every positive-support vector into ground and
strictly excited sectors. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectral_ground_add_excited
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundPositiveExtension
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugePositiveGroundCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) +
      finiteEvenFourTorusZ2UnfixedGaugeExcitedPositiveExtension
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugePositiveExcitedCoordinates
          H β energyIdentity energyNontrivial hβ hEnergy x) = x :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectral_ground_add_excited x

/-- Actual positive-support fixed vectors are exactly the zero-energy vectors
of the actual support Hamiltonian. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer_eq_self_iff_hamiltonian_eq_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x = x ↔
      finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
        H β energyIdentity energyNontrivial hβ hEnergy x = 0 :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralTransfer_eq_self_iff_hamiltonian_eq_zero x

/-- Side-two nonidentity forces a strictly excited mode or a null mode. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExcitedOrNullSpectralIndex_nonempty
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
          0 β energyIdentity energyNontrivial hβ hEnergy) ∨
      Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
          0 β energyIdentity energyNontrivial hβ hEnergy) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    0 β energyIdentity energyNontrivial hβ hEnergy).nonempty_excited_or_null_of_operator_ne_one
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_ne_identity
        β energyIdentity energyNontrivial hβ hEnergy)

/-- Conditional actual finite-volume excitation gap. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeExcitationGap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    [Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ hEnergy)] : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitationGap

/-- Whenever an actual excited mode exists, its exact finite-volume gap is
strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExcitationGap_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    [Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ hEnergy)] :
    0 < finiteEvenFourTorusZ2UnfixedGaugeExcitationGap
      H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitationGap_pos

/-- Actual excited coordinates obey the exact conditional finite-gap decay
bound at every natural time. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_excitedSemigroup_coordinate_abs_le_gap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    [Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ hEnergy)]
    (n : ℕ)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    |finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy n x i.toPositive| ≤
      (Real.exp
        (-finiteEvenFourTorusZ2UnfixedGaugeExcitationGap
          H β energyIdentity energyNontrivial hβ hEnergy)) ^ n *
        |x i.toPositive| :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).excitedSemigroup_coordinate_abs_le_gap n x i

end

end MathlibAnalytic
end MGAP4D
