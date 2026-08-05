import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedResidualTiltComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spatial half-action directly on a lower-slice configuration. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (1 / 2 : ℝ) *
    finiteEvenFourTorusZ2SpatialWilsonAction
      H energyIdentity energyNontrivial A

/-- Embed a lower slice into the augmented state with the identity temporal
field.  This is used only to reuse the already proved exact shared-plaquette
mixed-action geometry. -/
def finiteEvenFourTorusZ2LiftLowerSlice
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteEvenFourTorusZ2AugmentedConfiguration H :=
  finiteEvenFourTorusZ2EncodeAugmentedConfiguration H
    (1 : FiniteEvenFourTorusZ2TemporalLinkField H) A

@[simp] theorem finiteEvenFourTorusZ2AugmentedLowerSlice_liftLowerSlice
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2AugmentedLowerSlice H
        (finiteEvenFourTorusZ2LiftLowerSlice H A) = A := by
  rfl

/-- Lower-slice replacement commutes exactly with the augmented identity-field
embedding. -/
@[simp] theorem finiteEvenFourTorusZ2LiftLowerSlice_update
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2LiftLowerSlice H (Function.update A source g) =
      Function.update
        (finiteEvenFourTorusZ2LiftLowerSlice H A) (Sum.inr source) g := by
  funext coordinate
  cases coordinate with
  | inl vertex =>
      simp [finiteEvenFourTorusZ2LiftLowerSlice,
        finiteEvenFourTorusZ2EncodeAugmentedConfiguration]
  | inr link =>
      by_cases hLink : link = source
      · subst link
        simp [finiteEvenFourTorusZ2LiftLowerSlice,
          finiteEvenFourTorusZ2EncodeAugmentedConfiguration]
      · simp [finiteEvenFourTorusZ2LiftLowerSlice,
          finiteEvenFourTorusZ2EncodeAugmentedConfiguration, hLink]

/-- Agreement off one lower source lifts to agreement off the corresponding
augmented lower coordinate. -/
theorem finiteEvenFourTorusZ2LiftLowerSlice_agreeOff
    (H : ℕ)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff A C source) :
    FiniteProductAgreeOff
      (finiteEvenFourTorusZ2LiftLowerSlice H A)
      (finiteEvenFourTorusZ2LiftLowerSlice H C)
      (Sum.inr source) := by
  intro coordinate hCoordinate
  cases coordinate with
  | inl vertex =>
      rfl
  | inr link =>
      have hLink : link ≠ source := by
        intro hEq
        apply hCoordinate
        exact congrArg Sum.inr hEq
      exact hAgree link hLink

/-- The slice half-action mixed difference is exactly the already formalized
augmented lower spatial half-action mixed difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction_mixedDifference_eq_augmented
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
          H energyIdentity energyNontrivial)
        A C target g h =
      finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
          H energyIdentity energyNontrivial)
        (finiteEvenFourTorusZ2LiftLowerSlice H A)
        (finiteEvenFourTorusZ2LiftLowerSlice H C)
        (Sum.inr target) g h := by
  unfold finitePositiveWeightMixedActionDifference
  rw [← finiteEvenFourTorusZ2LiftLowerSlice_update,
    ← finiteEvenFourTorusZ2LiftLowerSlice_update,
    ← finiteEvenFourTorusZ2LiftLowerSlice_update,
    ← finiteEvenFourTorusZ2LiftLowerSlice_update]
  rfl

/-- Exact-support all-volume mixed-action radius for the extracted Perron
sandwich local factor. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
    H energyIdentity energyNontrivial target (Sum.inr source)

/-- The extracted Perron local mixed-action radius is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
      H energyIdentity energyNontrivial target source := by
  exact
    finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius_nonneg
      H energyIdentity energyNontrivial hEnergy target (Sum.inr source)

/-- The actual slice half-action inherits the exact shared-plaquette support
and the all-volume radius `12 * energySpread`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction_uniform_mixedAction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source) :
    FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
        H energyIdentity energyNontrivial)
      A C target
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
        H energyIdentity energyNontrivial target source) := by
  intro g h
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction_mixedDifference_eq_augmented]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction_uniform_mixedAction
      H energyIdentity energyNontrivial hEnergy target (Sum.inr source)
      (finiteEvenFourTorusZ2LiftLowerSlice H A)
      (finiteEvenFourTorusZ2LiftLowerSlice H C)
      (by
        intro hEq
        exact hNe (Sum.inr.inj hEq))
      (finiteEvenFourTorusZ2LiftLowerSlice_agreeOff
        H A C source hAgree)
      g h

/-- The extracted Perron sandwich local factor is a common positive scale
multiplying the exponential of the slice spatial half-action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_eq_scaledExponential
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
        H β energyIdentity energyNontrivial hβ hEnergy =
      fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale
            H β energyIdentity energyNontrivial hβ hEnergy *
          Real.exp
            (-β *
              finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
                H energyIdentity energyNontrivial A) := by
  funext A
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
    finiteEvenFourTorusZ2SpatialHalfWeight
    finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
  congr 2
  ring

/-- Physical exponential radius contributed by the extracted Perron local
half-weight factor. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  β * finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
    H energyIdentity energyNontrivial target source

/-- The physical local Perron cross-ratio radius is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
      H β energyIdentity energyNontrivial target source := by
  exact mul_nonneg hβ
    (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius_nonneg
      H energyIdentity energyNontrivial hEnergy target source)

/-- The extracted Perron local factor now has an actual exact-support
cross-ratio row; no abstract local Perron input remains. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_crossRatio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      A C target
      (Real.exp
        (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
          H β energyIdentity energyNontrivial target source)) := by
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_eq_scaledExponential]
  simpa [
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius] using
    finitePositiveScaledExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
      (finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
        H energyIdentity energyNontrivial)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalScale
        H β energyIdentity energyNontrivial hβ hEnergy)
      β hβ A C target
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
        H energyIdentity energyNontrivial target source)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction_uniform_mixedAction
        H energyIdentity energyNontrivial hEnergy A C target source hNe hAgree)

end

end MathlibAnalytic
end MGAP4D
