import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundExcitationProperties

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Complete side-two ground/excitation/null spectral package for the actual
finite `Z₂` Gauss-invariant unfixed-gauge one-slab transfer.  The package
records a conditional excited-sector gap rather than asserting that the
excited sector is unconditionally nonempty. -/
structure Z2UnfixedGaugeGroundExcitationCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  invariantTransfer_norm_eq_one :
    ‖finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      0 β energyIdentity energyNontrivial hβ hEnergy‖ = 1
  ground_nonempty :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
        0 β energyIdentity energyNontrivial hβ hEnergy)
  positiveSupport_decomposition :
    ∀ x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      0 β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugeGroundPositiveExtension
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugePositiveGroundCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x) +
        finiteEvenFourTorusZ2UnfixedGaugeExcitedPositiveExtension
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugePositiveExcitedCoordinates
            0 β energyIdentity energyNontrivial hβ hEnergy x) = x
  fixed_iff_zeroEnergy :
    ∀ x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      0 β energyIdentity energyNontrivial hβ hEnergy,
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy x = x ↔
        finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
          0 β energyIdentity energyNontrivial hβ hEnergy x = 0
  excited_or_null_nonempty :
    Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
          0 β energyIdentity energyNontrivial hβ hEnergy) ∨
      Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
          0 β energyIdentity energyNontrivial hβ hEnergy)
  conditional_excitationGap :
    Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
          0 β energyIdentity energyNontrivial hβ hEnergy) →
      ∃ Δ : ℝ,
        0 < Δ ∧
        ∀ (n : ℕ)
          (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
            0 β energyIdentity energyNontrivial hβ hEnergy)
          (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
            0 β energyIdentity energyNontrivial hβ hEnergy),
          |finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
              0 β energyIdentity energyNontrivial hβ hEnergy n x i.toPositive| ≤
            (Real.exp (-Δ)) ^ n * |x i.toPositive|

/-- The actual side-two transfer supplies the complete ground/excitation/null
spectral package. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundExcitationCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2UnfixedGaugeGroundExcitationCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { invariantTransfer_norm_eq_one :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_eq_one
        0 β energyIdentity energyNontrivial hβ hEnergy
    ground_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_nonempty
        0 β energyIdentity energyNontrivial hβ hEnergy
    positiveSupport_decomposition :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectral_ground_add_excited
        0 β energyIdentity energyNontrivial hβ hEnergy
    fixed_iff_zeroEnergy :=
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer_eq_self_iff_hamiltonian_eq_zero
        0 β energyIdentity energyNontrivial hβ hEnergy
    excited_or_null_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeExcitedOrNullSpectralIndex_nonempty
        β energyIdentity energyNontrivial hβ hEnergy
    conditional_excitationGap := by
      intro hExcited
      letI : Nonempty
          (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
            0 β energyIdentity energyNontrivial hβ hEnergy) := hExcited
      refine ⟨finiteEvenFourTorusZ2UnfixedGaugeExcitationGap
        0 β energyIdentity energyNontrivial hβ hEnergy, ?_, ?_⟩
      · exact finiteEvenFourTorusZ2UnfixedGaugeExcitationGap_pos
          0 β energyIdentity energyNontrivial hβ hEnergy
      · intro n x i
        exact finiteEvenFourTorusZ2UnfixedGauge_excitedSemigroup_coordinate_abs_le_gap
          0 β energyIdentity energyNontrivial hβ hEnergy n x i }

end

end MathlibAnalytic
end MGAP4D
