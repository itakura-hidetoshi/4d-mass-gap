import MGAP4D.MathlibAnalytic.SecondOrderExpansionFromDerivativeProfile
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabKernelSecondVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronKernelContinuity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferIntertwining
import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementMixedDifferenceWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace
open scoped BigOperators

noncomputable section

/-- Four-point mixed difference of the proof-free analytic one-slab kernel. -/
noncomputable def finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (β : ℝ) : ℝ :=
  finiteKernelMixedCrossDifference
    (fun A B =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
        H energyIdentity energyNontrivial β A B)
    x x' y y'

/-- Four-point mixed difference of the named all-beta first-variation profile. -/
noncomputable def finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (β : ℝ) : ℝ :=
  finiteKernelMixedCrossDifference
    (fun A B =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
        H energyIdentity energyNontrivial β A B)
    x x' y y'

/-- Four-point mixed difference of the exact non-factorial beta-zero slab
second moment. -/
noncomputable def finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteKernelMixedCrossDifference
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
      H energyIdentity energyNontrivial)
    x x' y y'

/-- The mixed first-profile is the actual derivative profile of the mixed
analytic kernel at every real coupling. -/
theorem finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference_hasDerivAt_named
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
        H energyIdentity energyNontrivial x x' y y')
      (finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
        H energyIdentity energyNontrivial x x' y y' β)
      β := by
  unfold finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
    finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
    finiteKernelMixedCrossDifference
  exact
    ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial β x y).sub
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial β x y')).sub
      ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial β x' y).sub
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial β x' y'))

@[simp] theorem finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
      H energyIdentity energyNontrivial x x' y y' 0 = 0 := by
  simp [finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference,
    finiteKernelMixedCrossDifference]

/-- Package T's boundary-additivity theorem says that the mixed derivative
profile also vanishes at beta zero. -/
theorem finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
      H energyIdentity energyNontrivial x x' y y' 0 = 0 := by
  unfold finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
    finiteKernelMixedCrossDifference
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero]
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right_independent
      H energyIdentity energyNontrivial x x' y y'
  linarith

/-- The derivative at beta zero of the mixed first-profile is exactly the mixed
second slab-action moment. -/
theorem finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
        H energyIdentity energyNontrivial x x' y y')
      (finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
        H energyIdentity energyNontrivial x x' y y')
      0 := by
  unfold finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
    finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
    finiteKernelMixedCrossDifference
  exact
    ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_hasDerivAt_zero
        H energyIdentity energyNontrivial x y).sub
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_hasDerivAt_zero
        H energyIdentity energyNontrivial x y')).sub
      ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_hasDerivAt_zero
        H energyIdentity energyNontrivial x' y).sub
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_hasDerivAt_zero
        H energyIdentity energyNontrivial x' y'))

/-- The actual finite-Z2 raw mixed difference has its full positive-side
second-order Peano expansion, derived from the already formalized Boltzmann
derivative profile. -/
theorem finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference_secondOrderExpansion
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasSecondOrderExpansionAtZero
      (finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
        H energyIdentity energyNontrivial x x' y y')
      (finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
        H energyIdentity energyNontrivial x x' y y') := by
  apply hasSecondOrderExpansionAtZero_of_derivativeProfile
    (g := finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference
      H energyIdentity energyNontrivial x x' y y')
  · intro β
    exact
      finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference_hasDerivAt_named
        H energyIdentity energyNontrivial β x x' y y'
  · exact finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference_zero
      H energyIdentity energyNontrivial x x' y y'
  · exact finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference_zero
      H energyIdentity energyNontrivial x x' y y'
  · exact
      finiteEvenFourTorusZ2OneSlabAnalyticFirstProfileMixedDifference_hasDerivAt_zero
        H energyIdentity energyNontrivial x x' y y'

/-- The analytic and continuity-oriented all-real kernel extensions are exactly
the same finite Boltzmann family. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
        H energyIdentity energyNontrivial β A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
    finiteBoltzmannWeightedProfile finiteBoltzmannWeightedSum
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
  apply congrArg
    (fun z : ℝ =>
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro U _hU
  simp only [mul_one]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_beta_independent
    H β 0 energyIdentity energyNontrivial U A B]
  congr 1
  ring

/-- Mixed difference of the proof-independent coupling family. -/
noncomputable def finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (β : ℝ) : ℝ :=
  finiteKernelMixedCrossDifference
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β)
    x x' y y'

/-- The two mixed-difference realizations agree pointwise. -/
theorem finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference_eq_analytic
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
        H energyIdentity energyNontrivial x x' y y' β =
      finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
        H energyIdentity energyNontrivial x x' y y' β := by
  unfold finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
    finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference
    finiteKernelMixedCrossDifference
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily]

/-- All-real operator-norm normalization scalar for the coupling family. -/
noncomputable def finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ) : ℝ :=
  ‖finiteKernelOperator
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β)‖⁻¹

/-- No normalization derivative is needed: the scalar normalization is already
continuous on all real couplings. -/
theorem continuous_finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Continuous
      (finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial) := by
  unfold finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
  exact
    (continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawPerronValue
      H energyIdentity energyNontrivial).inv₀
      (fun β => norm_ne_zero_iff.mpr
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_raw_ne_zero
          H energyIdentity energyNontrivial β))

/-- Exact beta-zero value of the all-real normalization scalar. -/
theorem finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial 0 =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := by
  unfold finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
  have hk :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial 0 =
        fun _ _ => (1 : ℝ) := by
    funext A B
    rw [← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily]
    exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero
      H energyIdentity energyNontrivial A B
  rw [hk, finiteKernelOperator_one_norm]

/-- Mixed difference of the actual operator-norm-normalized one-slab kernel. -/
noncomputable def finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (β : ℝ) : ℝ :=
  finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
      H energyIdentity energyNontrivial β *
    finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
      H energyIdentity energyNontrivial x x' y y' β

/-- Continuity of the normalization alone transports the raw quadratic
coefficient to the actual normalized transfer mixed difference.  Neither the
first nor the second derivative of the operator norm appears. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference_quadraticQuotient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference
            H energyIdentity energyNontrivial x x' y y' β / β ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (((Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
            H energyIdentity energyNontrivial x x' y y') / (2 : ℝ))) := by
  have hNorm :
      Tendsto
        (finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
          H energyIdentity energyNontrivial)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹) := by
    have h :=
      (continuous_finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial).continuousAt.tendsto
    have hWithin :
        Tendsto
          (finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
            H energyIdentity energyNontrivial)
          (nhdsWithin (0 : ℝ) (Ioi 0))
          (nhds
            (finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
              H energyIdentity energyNontrivial 0)) := by
      exact h.mono_left inf_le_left
    simpa [finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization_zero] using hWithin
  have hRaw :=
    (finiteEvenFourTorusZ2OneSlabAnalyticMixedDifference_secondOrderExpansion
      H energyIdentity energyNontrivial x x' y y').quadraticQuotient
  have hRaw' :
      Tendsto
        (fun β : ℝ =>
          finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
              H energyIdentity energyNontrivial x x' y y' β / β ^ 2)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds
          (finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
            H energyIdentity energyNontrivial x x' y y' / (2 : ℝ))) := by
    simpa only [finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference_eq_analytic]
      using hRaw
  have hMul := hNorm.mul hRaw'
  convert hMul using 1 <;>
    simp [finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference,
      div_eq_mul_inv] <;> ring

end

end MathlibAnalytic
end MGAP4D
