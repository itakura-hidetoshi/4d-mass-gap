import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingWitnessMinor
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSpectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual side-two excitation gap in the strict-coupling regime.  Unlike
the earlier conditional definition, the required nonempty excited-sector
instance is supplied by strict tensor positivity and null-sector absence. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) : ℝ := by
  letI : Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
    finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict
      β energyIdentity energyNontrivial hβ hEnergy
  exact finiteEvenFourTorusZ2UnfixedGaugeExcitationGap
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le

/-- The strict-coupling actual finite-volume excitation gap is positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap_pos
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap
      β energyIdentity energyNontrivial hβ hEnergy := by
  letI : Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
    finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict
      β energyIdentity energyNontrivial hβ hEnergy
  exact finiteEvenFourTorusZ2UnfixedGaugeExcitationGap_pos
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le

/-- Every strictly excited coordinate of the actual side-two transfer obeys
an unconditional exponential natural-time bound in the strict-coupling
regime. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeStrict_excitedSemigroup_coordinate_abs_le_gap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (n : ℕ)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :
    |finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le n x i.toPositive| ≤
      (Real.exp
        (-finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap
          β energyIdentity energyNontrivial hβ hEnergy)) ^ n *
        |x i.toPositive| := by
  letI : Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
    finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict
      β energyIdentity energyNontrivial hβ hEnergy
  exact finiteEvenFourTorusZ2UnfixedGauge_excitedSemigroup_coordinate_abs_le_gap
    0 β energyIdentity energyNontrivial hβ.le hEnergy.le n x i

/-- Every actual strict-coupling excited mode has finite strictly positive
extended spectral energy. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeStrict_excited_extendedEnergy_finite_pos
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le) :
    finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.1 =
      ExtendedSpectralEnergy.finite
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive) ∧
    0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive :=
  ⟨finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_excited
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le i,
    finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy_excited_pos
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le i⟩

/-- Complete strict-coupling side-two spectral package for the actual finite
`Z₂` Gauss-invariant unfixed-gauge one-slab transfer.

This integrates, in one mathematical unit:

* strict local two-state positive definiteness;
* positive definiteness of the complete finite tensor crossing kernel;
* preservation under the positive spatial sandwich;
* injectivity of the temporal and compressed invariant transfers;
* absence of all null spectral modes at every finite side parameter;
* Perron uniqueness of the ground ray;
* unconditional nonemptiness of the side-two strictly excited sector;
* a positive finite-volume excitation gap and exact exponential decay;
* the complete ground/excited/null natural-time and extended-energy package. -/
structure Z2UnfixedGaugeStrictCouplingSpectralGapCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  perronGroundPackage :
    Z2UnfixedGaugePerronGroundCompletePackage
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  fullSpectralPackage :
    Z2UnfixedGaugeFullSpectralCompletePackage
      β energyIdentity energyNontrivial hβ.le hEnergy.le
  temporalRawTransfer_injective :
    Function.Injective
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
  invariantTransfer_injective :
    Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
  null_not_nonempty :
    ¬ Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
  excited_nonempty :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
  strictExcitationGap_pos :
    0 < finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap
      β energyIdentity energyNontrivial hβ hEnergy
  excited_coordinate_decay :
    ∀ (n : ℕ)
      (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le),
      |finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le n x i.toPositive| ≤
        (Real.exp
          (-finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap
            β energyIdentity energyNontrivial hβ hEnergy)) ^ n *
          |x i.toPositive|
  excited_extendedEnergy_finite_pos :
    ∀ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le,
      finiteEvenFourTorusZ2UnfixedGaugeExtendedSpectralEnergy
          0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.1 =
        ExtendedSpectralEnergy.finite
          (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
            0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive) ∧
      0 < finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive

/-- Construct the complete strict-coupling actual side-two spectral package. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeStrictCouplingSpectralGapCompletePackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2UnfixedGaugeStrictCouplingSpectralGapCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { perronGroundPackage :=
      finiteEvenFourTorusZ2UnfixedGaugePerronGroundCompletePackage
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le
    fullSpectralPackage :=
      finiteEvenFourTorusZ2UnfixedGaugeFullSpectralCompletePackage
        β energyIdentity energyNontrivial hβ.le hEnergy.le
    temporalRawTransfer_injective :=
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_injective_strict
        0 β energyIdentity energyNontrivial hβ hEnergy
    invariantTransfer_injective :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_injective_strict
        0 β energyIdentity energyNontrivial hβ hEnergy
    null_not_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
        0 β energyIdentity energyNontrivial hβ hEnergy
    excited_nonempty :=
      finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict
        β energyIdentity energyNontrivial hβ hEnergy
    strictExcitationGap_pos :=
      finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGap_pos
        β energyIdentity energyNontrivial hβ hEnergy
    excited_coordinate_decay :=
      finiteEvenFourTorusZ2UnfixedGaugeStrict_excitedSemigroup_coordinate_abs_le_gap
        β energyIdentity energyNontrivial hβ hEnergy
    excited_extendedEnergy_finite_pos :=
      finiteEvenFourTorusZ2UnfixedGaugeStrict_excited_extendedEnergy_finite_pos
        β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
