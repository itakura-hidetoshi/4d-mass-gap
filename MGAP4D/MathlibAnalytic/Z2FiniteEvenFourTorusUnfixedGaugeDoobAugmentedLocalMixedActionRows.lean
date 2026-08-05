import MGAP4D.MathlibAnalytic.FinitePositiveWeightExponentialMixedActionCrossRatio
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedInternalCrossRatioRows
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual reduced local one-slab action regarded as a function of the
encoded augmented configuration. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
    H β energyIdentity energyNontrivial
    (finiteEvenFourTorusZ2AugmentedTemporalField H X)
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- The actual encoded reduced local factor is a common scalar multiple of the
exponential of the encoded reduced local action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_eq_scaledExponential
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B =
      fun X : FiniteEvenFourTorusZ2AugmentedConfiguration H =>
        (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          Real.exp
            (-β *
              finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
                H β energyIdentity energyNontrivial B X) := by
  rfl

/-- A mixed oscillation bound for the actual reduced local action gives the
corresponding cross-ratio bound for the actual encoded local factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_crossRatio_of_mixedAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (radius : ℝ)
    (hMixed : FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B)
      X Y target radius) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      X Y target (Real.exp (β * radius)) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_eq_scaledExponential]
  exact
    finitePositiveScaledExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B)
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹
      β hβ X Y target radius hMixed

/-- Local mixed-action row data for the actual augmented one-slab action.
Temporal targets and lower-link targets retain separate geometric radii so
that later finite-neighborhood proofs can be compiled independently. -/
structure Z2AugmentedLocalMixedActionRowsData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) where
  temporalLocalRadius :
    FiniteEvenFourTorusSpatialVertex H →
      FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ
  temporalLocalRadius_nonneg :
    ∀ target source, 0 ≤ temporalLocalRadius target source
  temporalMixedAction :
    ∀ (target : FiniteEvenFourTorusSpatialVertex H)
      (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
      (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H),
      Sum.inl target ≠ source →
      FiniteProductAgreeOff X Y source →
        FinitePositiveWeightMixedActionOscillationBound
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
            H β energyIdentity energyNontrivial B)
          X Y (Sum.inl target) (temporalLocalRadius target source)
  lowerLocalRadius :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ
  lowerLocalRadius_nonneg :
    ∀ target source, 0 ≤ lowerLocalRadius target source
  lowerMixedAction :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
      (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H),
      Sum.inr target ≠ source →
      FiniteProductAgreeOff X Y source →
        FinitePositiveWeightMixedActionOscillationBound
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
            H β energyIdentity energyNontrivial B)
          X Y (Sum.inr target) (lowerLocalRadius target source)

namespace Z2AugmentedLocalMixedActionRowsData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {B : FiniteEvenFourTorusZ2SliceConfiguration H}

/-- The local radius on the full augmented coordinate sum. -/
def assembledLocalRadius
    (D : Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  match target with
  | Sum.inl targetVertex => D.temporalLocalRadius targetVertex source
  | Sum.inr targetLink => D.lowerLocalRadius targetLink source

/-- Every assembled local mixed-action radius is nonnegative. -/
theorem assembledLocalRadius_nonneg
    (D : Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ D.assembledLocalRadius target source := by
  cases target with
  | inl targetVertex =>
      exact D.temporalLocalRadius_nonneg targetVertex source
  | inr targetLink =>
      exact D.lowerLocalRadius_nonneg targetLink source

/-- The separated actual temporal/lower data form a generic rowwise
mixed-action package on the augmented coordinate type. -/
def toMixedActionRows
    (D : Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B) :
    FinitePositiveExponentialWeightMixedActionRows
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B) :=
  { radius := D.assembledLocalRadius
    radius_nonneg := D.assembledLocalRadius_nonneg
    mixedActionBound := by
      intro target source X Y hNe hAgree
      cases target with
      | inl targetVertex =>
          exact D.temporalMixedAction targetVertex source X Y hNe hAgree
      | inr targetLink =>
          exact D.lowerMixedAction targetLink source X Y hNe hAgree }

/-- Temporal local cross-ratio rows are now consequences of temporal mixed
crossing-action oscillation bounds. -/
theorem temporalLocalCrossRatio
    (D : Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B)
    (hβ : 0 ≤ β)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : Sum.inl target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inl target)
      (Real.exp (β * D.temporalLocalRadius target source)) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_crossRatio_of_mixedAction
      H β energyIdentity energyNontrivial hβ B X Y (Sum.inl target)
      (D.temporalLocalRadius target source)
      (D.temporalMixedAction target source X Y hNe hAgree)

/-- Lower-link local cross-ratio rows are consequences of the combined local
spatial/crossing mixed-action oscillation bounds. -/
theorem lowerLocalCrossRatio
    (D : Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B)
    (hβ : 0 ≤ β)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : Sum.inr target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inr target)
      (Real.exp (β * D.lowerLocalRadius target source)) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_crossRatio_of_mixedAction
      H β energyIdentity energyNontrivial hβ B X Y (Sum.inr target)
      (D.lowerLocalRadius target source)
      (D.lowerMixedAction target source X Y hNe hAgree)

/-- Compile actual local mixed-action rows together with an independently
proved lower Perron row into the existing full internal row assembly.  The
stored internal radii are the physical exponential radii `β * M`. -/
def toInternalCrossRatioRowsData
    (D : Z2AugmentedLocalMixedActionRowsData
      H β energyIdentity energyNontrivial B)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
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
  { temporalLocalRadius := fun target source =>
      β * D.temporalLocalRadius target source
    temporalLocalRadius_nonneg := fun target source =>
      mul_nonneg hβ (D.temporalLocalRadius_nonneg target source)
    temporalLocalCrossRatio := by
      intro target source X Y hNe hAgree
      exact D.temporalLocalCrossRatio hβ target source X Y hNe hAgree
    lowerLocalRadius := fun target source =>
      β * D.lowerLocalRadius target source
    lowerLocalRadius_nonneg := fun target source =>
      mul_nonneg hβ (D.lowerLocalRadius_nonneg target source)
    lowerLocalCrossRatio := by
      intro target source X Y hNe hAgree
      exact D.lowerLocalCrossRatio hβ target source X Y hNe hAgree
    lowerPerronRadius := lowerPerronRadius
    lowerPerronRadius_nonneg := lowerPerronRadius_nonneg
    lowerPerronCrossRatio := lowerPerronCrossRatio }

end Z2AugmentedLocalMixedActionRowsData

end

end MathlibAnalytic
end MGAP4D
