import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedLowerCrossingMixedAction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual encoded reduced local action is exactly the sum of the lower
spatial half-action and the crossing action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_eq_spatialHalf_add_crossing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B X =
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
          H energyIdentity energyNontrivial X +
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B X := by
  rfl

/-- The four-point mixed difference of the actual reduced local action splits
exactly into its lower spatial half-action and crossing contributions. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_mixedDifference_eq_spatialHalf_add_crossing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
          H β energyIdentity energyNontrivial B)
        X Y target g h =
      finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
            H energyIdentity energyNontrivial)
          X Y target g h +
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
            H β energyIdentity energyNontrivial B)
          X Y target g h := by
  unfold finitePositiveWeightMixedActionDifference
  simp_rw [
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_eq_spatialHalf_add_crossing]
  ring

/-- The exact-support lower local radius is the sum of the lower spatial
half-action radius and the lower crossing radius. -/
def finiteEvenFourTorusZ2LowerLocalMixedActionRadius
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
      H energyIdentity energyNontrivial target source +
    finiteEvenFourTorusZ2LowerCrossingMixedActionRadius
      H energyIdentity energyNontrivial target source

/-- The assembled lower local radius is nonnegative. -/
theorem finiteEvenFourTorusZ2LowerLocalMixedActionRadius_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ finiteEvenFourTorusZ2LowerLocalMixedActionRadius
      H energyIdentity energyNontrivial target source := by
  exact add_nonneg
    (finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius_nonneg
      H energyIdentity energyNontrivial hEnergy target source)
    (finiteEvenFourTorusZ2LowerCrossingMixedActionRadius_nonneg
      H energyIdentity energyNontrivial hEnergy target source)

/-- The actual reduced local action has a fully explicit lower-link
mixed-action row: the finite-range spatial half-action row plus the exact
three-coordinate crossing row. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_lower_mixedAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : Sum.inr target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inr target)
      (finiteEvenFourTorusZ2LowerLocalMixedActionRadius
        H energyIdentity energyNontrivial target source) := by
  intro g h
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_mixedDifference_eq_spatialHalf_add_crossing]
  calc
    |finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
            H energyIdentity energyNontrivial)
          X Y (Sum.inr target) g h +
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
            H β energyIdentity energyNontrivial B)
          X Y (Sum.inr target) g h| ≤
      |finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
            H energyIdentity energyNontrivial)
          X Y (Sum.inr target) g h| +
        |finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
            H β energyIdentity energyNontrivial B)
          X Y (Sum.inr target) g h| :=
      abs_add_le _ _
    _ ≤ finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
          H energyIdentity energyNontrivial target source +
        finiteEvenFourTorusZ2LowerCrossingMixedActionRadius
          H energyIdentity energyNontrivial target source := by
      exact add_le_add
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction_uniform_mixedAction
          H energyIdentity energyNontrivial hEnergy target source X Y
          hNe hAgree g h)
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedAction
          H β energyIdentity energyNontrivial hEnergy B target source X Y
          hNe hAgree g h)
    _ = finiteEvenFourTorusZ2LowerLocalMixedActionRadius
        H energyIdentity energyNontrivial target source := rfl

/-- The actual temporal and lower local action geometry now supplies the full
local mixed-action row data required by the generic exponential cross-ratio
and internal-row assembly layers. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobActualLocalMixedActionRowsData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B :=
  { temporalLocalRadius :=
      finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
        H energyIdentity energyNontrivial
    temporalLocalRadius_nonneg := by
      intro target source
      exact
        finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius_nonneg
          H energyIdentity energyNontrivial hEnergy target source
    temporalMixedAction := by
      intro target source X Y hNe hAgree
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_uniform_mixedAction
          H β energyIdentity energyNontrivial hEnergy B target source X Y
          hNe hAgree
    lowerLocalRadius :=
      finiteEvenFourTorusZ2LowerLocalMixedActionRadius
        H energyIdentity energyNontrivial
    lowerLocalRadius_nonneg := by
      intro target source
      exact
        finiteEvenFourTorusZ2LowerLocalMixedActionRadius_nonneg
          H energyIdentity energyNontrivial hEnergy target source
    lowerMixedAction := by
      intro target source X Y hNe hAgree
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_lower_mixedAction
          H β energyIdentity energyNontrivial hEnergy B target source X Y
          hNe hAgree }

/-- The actual lower local factor cross-ratio row is a consequence of the
assembled finite-range mixed-action data, with no abstract local row input. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_lower_crossRatio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : Sum.inr target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inr target)
      (Real.exp
        (β * finiteEvenFourTorusZ2LowerLocalMixedActionRadius
          H energyIdentity energyNontrivial target source)) := by
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeDoobActualLocalMixedActionRowsData
      H β energyIdentity energyNontrivial hEnergy B).lowerLocalCrossRatio
        hβ target source X Y hNe hAgree

/-- Once an independent lower Perron row is supplied, the actual local action
rows compile directly into the complete internal cross-ratio row data.  Thus
all remaining nonlocal input is isolated in the lower Perron factor. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobActualInternalCrossRatioRowsData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (lowerPerronRadius :
      FiniteEvenFourTorusSpatialLink H →
        FiniteEvenFourTorusSpatialLink H → ℝ)
    (lowerPerronRadius_nonneg :
      ∀ target source, 0 ≤ lowerPerronRadius target source)
    (lowerPerronCrossRatio :
      ∀ (target source : FiniteEvenFourTorusSpatialLink H)
        (A C : FiniteEvenFourTorusZ2SliceConfiguration H),
        target ≠ source →
        FiniteProductAgreeOff A C source →
          FinitePositiveWeightSingleSiteCrossRatioBound
            (fun Z : FiniteEvenFourTorusZ2SliceConfiguration H =>
              finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
                H β energyIdentity energyNontrivial hβ hEnergy Z)
            A C target (Real.exp (lowerPerronRadius target source))) :
    Z2AugmentedInternalCrossRatioRowsData
      H β energyIdentity energyNontrivial hβ hEnergy B :=
  (finiteEvenFourTorusZ2UnfixedGaugeDoobActualLocalMixedActionRowsData
    H β energyIdentity energyNontrivial hEnergy B).toInternalCrossRatioRowsData
      hβ hEnergy lowerPerronRadius lowerPerronRadius_nonneg
      lowerPerronCrossRatio

end

end MathlibAnalytic
end MGAP4D
