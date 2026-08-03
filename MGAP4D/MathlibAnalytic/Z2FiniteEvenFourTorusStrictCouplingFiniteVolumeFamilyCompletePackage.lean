import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingAllVolumeSpectralGap
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSpectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Complete strict-coupling spectral package at one arbitrary finite side
parameter.  Unlike the earlier side-two bundle, every field below is stated at
the displayed parameter `H`. -/
structure Z2UnfixedGaugeStrictCouplingAtVolumeCompletePackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  invariantTransfer_norm_eq_one :
    ‖finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ.le hEnergy.le‖ = 1
  positiveGroundRay :
    ∃ p : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      p ≠ 0 ∧
      FiniteBoundaryPointwisePositive p.1 ∧
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le p = p ∧
      ∀ g : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ.le hEnergy.le g = g →
          ∃ c : ℝ, g = c • p
  canonicalGroundIndex_unique :
    Nonempty
        (FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
          H β energyIdentity energyNontrivial hβ.le hEnergy.le) ∧
      Subsingleton
        (FiniteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  invariantTransfer_ne_identity :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ.le hEnergy.le ≠ 1
  temporalRawTransfer_injective :
    Function.Injective
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  invariantTransfer_injective :
    Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  null_not_nonempty :
    ¬ Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  excited_nonempty :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  ground_add_excited :
    ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralSynthesis
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
            H β energyIdentity energyNontrivial hβ.le hEnergy.le x) +
        finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralSynthesis
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteEvenFourTorusZ2UnfixedGaugeExcitedCoordinates
            H β energyIdentity energyNontrivial hβ.le hEnergy.le x) = x
  transfer_kernel_trivial :
    ∀ x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 ↔
        x = 0
  fullNaturalTime_zero :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
      H β energyIdentity energyNontrivial hβ.le hEnergy.le 0 = 1
  fullNaturalTime_one :
    finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
        H β energyIdentity energyNontrivial hβ.le hEnergy.le 1 =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  fullNaturalTime_add :
    ∀ m n : ℕ,
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          H β energyIdentity energyNontrivial hβ.le hEnergy.le (m + n) =
        (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          H β energyIdentity energyNontrivial hβ.le hEnergy.le m).comp
        (finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime
          H β energyIdentity energyNontrivial hβ.le hEnergy.le n)
  strictExcitationGap_pos :
    0 < finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGapAt
      H β energyIdentity energyNontrivial hβ hEnergy
  excited_coordinate_decay :
    ∀ (n : ℕ)
      (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le),
      |finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
          H β energyIdentity energyNontrivial hβ.le hEnergy.le n x i.toPositive| ≤
        (Real.exp
          (-finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGapAt
            H β energyIdentity energyNontrivial hβ hEnergy)) ^ n *
          |x i.toPositive|
  excited_extendedEnergy_finite_pos :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ.le hEnergy.le,
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
          H β energyIdentity energyNontrivial hβ.le hEnergy.le i.1 =
        ExtendedSpectralEnergy.finite
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
            H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive) ∧
      0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive

/-- Construct the complete strict-coupling package at one arbitrary finite
volume. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeStrictCouplingAtVolumeCompletePackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2UnfixedGaugeStrictCouplingAtVolumeCompletePackage
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { invariantTransfer_norm_eq_one :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_eq_one
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    positiveGroundRay :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_space_generated_by_positiveGround
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    canonicalGroundIndex_unique :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_unique
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    invariantTransfer_ne_identity :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_allVolume_ne_identity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    temporalRawTransfer_injective :=
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_injective_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    invariantTransfer_injective :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_injective_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    null_not_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    excited_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_allVolume_nonempty_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    ground_add_excited :=
      finiteEvenFourTorusZ2UnfixedGaugeStrict_allVolume_ground_add_excited
        H β energyIdentity energyNontrivial hβ hEnergy
    transfer_kernel_trivial :=
      finiteEvenFourTorusZ2UnfixedGaugeStrict_allVolume_transfer_eq_zero_iff
        H β energyIdentity energyNontrivial hβ hEnergy
    fullNaturalTime_zero :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_zero
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    fullNaturalTime_one :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_one
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    fullNaturalTime_add :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralNaturalTime_add
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    strictExcitationGap_pos :=
      finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGapAt_pos
        H β energyIdentity energyNontrivial hβ hEnergy
    excited_coordinate_decay :=
      finiteEvenFourTorusZ2UnfixedGaugeStrict_allVolume_excitedSemigroup_coordinate_abs_le_gap
        H β energyIdentity energyNontrivial hβ hEnergy
    excited_extendedEnergy_finite_pos :=
      finiteEvenFourTorusZ2UnfixedGaugeStrict_allVolume_excited_extendedEnergy_finite_pos
        H β energyIdentity energyNontrivial hβ hEnergy }

/-- One family-level theorem object collecting the complete package for every
finite side parameter.  It deliberately contains no uniform lower bound for
the volume-dependent gaps. -/
structure Z2UnfixedGaugeStrictCouplingFiniteVolumeFamilyCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  atVolume :
    ∀ H : ℕ,
      Z2UnfixedGaugeStrictCouplingAtVolumeCompletePackage
        H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete strict-coupling finite-volume family. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeStrictCouplingFiniteVolumeFamilyCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2UnfixedGaugeStrictCouplingFiniteVolumeFamilyCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { atVolume := fun H =>
      finiteEvenFourTorusZ2UnfixedGaugeStrictCouplingAtVolumeCompletePackage
        H β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
