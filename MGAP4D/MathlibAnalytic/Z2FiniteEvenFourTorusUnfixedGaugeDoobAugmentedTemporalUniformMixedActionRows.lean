import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedTemporalCrossingIncidenceBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The all-volume temporal local mixed-action radius.  It retains the exact
finite interaction support and replaces the target-dependent incident count
by the uniform bound six. -/
def finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  if source ∈
      finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood H target then
    12 * (energyNontrivial - energyIdentity)
  else 0

/-- The exact incident-cardinality radius is bounded by the all-volume radius. -/
theorem finiteEvenFourTorusZ2TemporalLocalMixedActionRadius_le_uniform
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    finiteEvenFourTorusZ2TemporalLocalMixedActionRadius
        H energyIdentity energyNontrivial target source ≤
      finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
        H energyIdentity energyNontrivial target source := by
  unfold finiteEvenFourTorusZ2TemporalLocalMixedActionRadius
    finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
  by_cases hSource : source ∈
      finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood H target
  · rw [if_pos hSource, if_pos hSource]
    have hCard :=
      finiteEvenFourTorusZ2TemporalTargetCrossingLinks_card_le_six H target
    have hCardReal :
        ((finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target).card : ℝ) ≤ 6 := by
      exact_mod_cast hCard
    have hSpread : 0 ≤ energyNontrivial - energyIdentity :=
      sub_nonneg.mpr hEnergy
    nlinarith
  · rw [if_neg hSource, if_neg hSource]

/-- The all-volume temporal radius is nonnegative. -/
theorem finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
      H energyIdentity energyNontrivial target source := by
  unfold finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
  split
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hEnergy)
  · exact le_rfl

/-- The actual reduced local action has an all-volume temporal mixed-action
row with exact finite support and radius `12 * energySpread`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_uniform_mixedAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : Sum.inl target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inl target)
      (finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
        H energyIdentity energyNontrivial target source) := by
  intro g h
  exact le_trans
    (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_mixedAction
      H β energyIdentity energyNontrivial hEnergy B target source X Y
      hNe hAgree g h)
    (finiteEvenFourTorusZ2TemporalLocalMixedActionRadius_le_uniform
      H energyIdentity energyNontrivial hEnergy target source)

/-- The all-volume temporal mixed-action row compiles directly into the actual
encoded local-factor cross-ratio row. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_temporal_uniform_crossRatio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : Sum.inl target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inl target)
      (Real.exp
        (β * finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
          H energyIdentity energyNontrivial target source)) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_crossRatio_of_mixedAction
      H β energyIdentity energyNontrivial hβ B X Y (Sum.inl target)
      (finiteEvenFourTorusZ2TemporalUniformLocalMixedActionRadius
        H energyIdentity energyNontrivial target source)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_uniform_mixedAction
        H β energyIdentity energyNontrivial hEnergy B target source X Y
        hNe hAgree)

end

end MathlibAnalytic
end MGAP4D
