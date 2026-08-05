import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedLowerSpatialMixedAction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact source neighborhood for the crossing contribution to a fixed
lower-link target.  Only the target crossing plaquette can contain that lower
coordinate, so this is precisely its three-coordinate support. -/
def finiteEvenFourTorusZ2LowerCrossingInteractionNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    Finset (FiniteEvenFourTorusZ2AugmentedCoordinate H) :=
  finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H target

@[simp] theorem finiteEvenFourTorusZ2_lowerTarget_mem_lowerCrossingInteractionNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    Sum.inr target ∈
      finiteEvenFourTorusZ2LowerCrossingInteractionNeighborhood H target := by
  simp [finiteEvenFourTorusZ2LowerCrossingInteractionNeighborhood,
    finiteEvenFourTorusZ2AugmentedCrossingLinkSupport]

/-- A lower coordinate belongs to one crossing-link support exactly when it is
that crossing link's own lower link. -/
theorem finiteEvenFourTorusZ2_lower_mem_augmentedCrossingLinkSupport_iff
    (H : ℕ)
    (target e : FiniteEvenFourTorusSpatialLink H) :
    Sum.inr target ∈ finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e ↔
      target = e := by
  simp [finiteEvenFourTorusZ2AugmentedCrossingLinkSupport]

/-- For a lower-link target, the full crossing-action mixed difference is
exactly the mixed difference of the single crossing link with the same index. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_eq_targetLink
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inr target) g h =
      finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B target)
        X Y (Sum.inr target) g h := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_mixedDifference_eq_sum]
  classical
  apply Finset.sum_eq_single target
  · intro e _he hNe
    apply
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_eq_zero_of_target_not_mem
    intro hMem
    exact hNe
      ((finiteEvenFourTorusZ2_lower_mem_augmentedCrossingLinkSupport_iff
        H target e).1 hMem).symm
  · simp

/-- If the changed source is outside the target crossing-link support, the
lower-target crossing mixed difference vanishes exactly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_eq_zero_of_source_not_mem
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hSource : source ∉
      finiteEvenFourTorusZ2LowerCrossingInteractionNeighborhood H target)
    (hAgree : FiniteProductAgreeOff X Y source) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inr target) g h = 0 := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_eq_targetLink]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_eq_zero_of_source_not_mem
      H energyIdentity energyNontrivial B target X Y
      (Sum.inr target) source g h hSource hAgree

/-- The lower-target crossing mixed difference has the single-link bound
`2 * energySpread`, independently of volume. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_abs_le_two_energySpread
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    |finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inr target) g h| ≤
      2 * (energyNontrivial - energyIdentity) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_eq_targetLink]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_abs_le_two_energySpread
      H energyIdentity energyNontrivial hEnergy B target X Y
      (Sum.inr target) g h

/-- Exact-support all-volume radius for the lower crossing contribution. -/
def finiteEvenFourTorusZ2LowerCrossingMixedActionRadius
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  if source ∈
      finiteEvenFourTorusZ2LowerCrossingInteractionNeighborhood H target then
    2 * (energyNontrivial - energyIdentity)
  else 0

/-- The lower crossing radius is nonnegative. -/
theorem finiteEvenFourTorusZ2LowerCrossingMixedActionRadius_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ finiteEvenFourTorusZ2LowerCrossingMixedActionRadius
      H energyIdentity energyNontrivial target source := by
  unfold finiteEvenFourTorusZ2LowerCrossingMixedActionRadius
  split
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hEnergy)
  · exact le_rfl

/-- The actual lower crossing action has exact three-coordinate support and
volume-independent mixed-action radius `2 * energySpread`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (_hNe : Sum.inr target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inr target)
      (finiteEvenFourTorusZ2LowerCrossingMixedActionRadius
        H energyIdentity energyNontrivial target source) := by
  intro g h
  by_cases hSource : source ∈
      finiteEvenFourTorusZ2LowerCrossingInteractionNeighborhood H target
  · rw [finiteEvenFourTorusZ2LowerCrossingMixedActionRadius, if_pos hSource]
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_abs_le_two_energySpread
        H β energyIdentity energyNontrivial hEnergy B X Y target g h
  · rw [
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_lower_mixedDifference_eq_zero_of_source_not_mem
        H β energyIdentity energyNontrivial B X Y target source g h
        hSource hAgree,
      abs_zero,
      finiteEvenFourTorusZ2LowerCrossingMixedActionRadius,
      if_neg hSource]

end

end MathlibAnalytic
end MGAP4D
