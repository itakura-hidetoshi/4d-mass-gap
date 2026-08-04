import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedLocalMixedActionRows
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The three augmented coordinates used by one temporal crossing plaquette:
the temporal links at its tail and head and its lower spatial link. -/
def finiteEvenFourTorusZ2AugmentedCrossingLinkSupport
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Finset (FiniteEvenFourTorusZ2AugmentedCoordinate H) :=
  { Sum.inl e.1,
    Sum.inl (finiteEvenFourTorusSpatialVertexStep H e.1 e.2),
    Sum.inr e }

/-- One local crossing energy as a function of the encoded augmented state. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
    H energyIdentity energyNontrivial
    (finiteEvenFourTorusZ2AugmentedTemporalField H X)
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B e

/-- The encoded crossing-link energy depends only on its exact three-coordinate
support. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_eq_of_agree_support
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hAgree :
      ∀ coordinate ∈
          finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e,
        X coordinate = Y coordinate) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
        H energyIdentity energyNontrivial B e X =
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
        H energyIdentity energyNontrivial B e Y := by
  have hTail := hAgree (Sum.inl e.1) (by
    simp [finiteEvenFourTorusZ2AugmentedCrossingLinkSupport])
  have hHead := hAgree
    (Sum.inl (finiteEvenFourTorusSpatialVertexStep H e.1 e.2)) (by
      simp [finiteEvenFourTorusZ2AugmentedCrossingLinkSupport])
  have hLower := hAgree (Sum.inr e) (by
    simp [finiteEvenFourTorusZ2AugmentedCrossingLinkSupport])
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
    finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
    finiteEvenFourTorusZ2AugmentedTemporalField
    finiteEvenFourTorusZ2AugmentedLowerSlice
  rw [hTail, hHead, hLower]

/-- Updating a coordinate outside one crossing-link support leaves its local
energy unchanged exactly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_update_eq_of_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (coordinate : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g : Z2Gauge)
    (hNot : coordinate ∉
      finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
        H energyIdentity energyNontrivial B e
        (Function.update X coordinate g) =
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
        H energyIdentity energyNontrivial B e X := by
  apply
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_eq_of_agree_support
  intro other hOther
  by_cases hEq : other = coordinate
  · subst other
    exact (hNot hOther).elim
  · simp [Function.update, hEq]

/-- The encoded crossing action on the augmented product state. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
    H β energyIdentity energyNontrivial
    (finiteEvenFourTorusZ2AugmentedTemporalField H X)
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- The encoded crossing action is exactly the sum of the encoded local
crossing-link energies. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_eq_sum_linkEnergy
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
        H β energyIdentity energyNontrivial B X =
      ∑ e : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e X := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
  exact
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_sum_linkEnergy
      H β energyIdentity energyNontrivial
      (finiteEvenFourTorusZ2AugmentedTemporalField H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Four-point mixed differences commute exactly with the finite crossing-link
sum. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_mixedDifference_eq_sum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y target g h =
      ∑ e : FiniteEvenFourTorusSpatialLink H,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e)
          X Y target g h := by
  unfold finitePositiveWeightMixedActionDifference
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_eq_sum_linkEnergy]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]

/-- A local crossing-link mixed difference is zero when the target coordinate
is outside that link's support. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_eq_zero_of_target_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hTarget : target ∉
      finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e)
        X Y target g h = 0 := by
  unfold finitePositiveWeightMixedActionDifference
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial B e X target g hTarget,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial B e Y target h hTarget,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial B e Y target g hTarget,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial B e X target h hTarget]
  ring

/-- If two environments differ only at a source outside one crossing-link
support, then that local link has zero target/source mixed difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_eq_zero_of_source_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hSource : source ∉
      finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e)
    (hAgree : FiniteProductAgreeOff X Y source) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e)
        X Y target g h = 0 := by
  have hEqG :
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e
          (Function.update X target g) =
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e
          (Function.update Y target g) := by
    apply
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_eq_of_agree_support
    intro coordinate hCoordinate
    by_cases hTarget : coordinate = target
    · subst coordinate
      simp
    · have hNeSource : coordinate ≠ source := by
        intro hEq
        subst coordinate
        exact hSource hCoordinate
      simp [Function.update, hTarget, hAgree coordinate hNeSource]
  have hEqH :
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e
          (Function.update Y target h) =
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e
          (Function.update X target h) := by
    apply
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_eq_of_agree_support
    intro coordinate hCoordinate
    by_cases hTarget : coordinate = target
    · subst coordinate
      simp
    · have hNeSource : coordinate ≠ source := by
        intro hEq
        subst coordinate
        exact hSource hCoordinate
      symm
      exact hAgree coordinate hNeSource
  unfold finitePositiveWeightMixedActionDifference
  rw [hEqG, hEqH]
  ring

/-- Every local two-level crossing energy has mixed oscillation at most twice
the energy spread. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_abs_le_two_energySpread
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge) :
    |finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e)
        X Y target g h| ≤
      2 * (energyNontrivial - energyIdentity) := by
  let Xg := Function.update X target g
  let Yg := Function.update Y target g
  let Xh := Function.update X target h
  let Yh := Function.update Y target h
  have hG :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_abs_sub_le_energySpread
      H energyIdentity energyNontrivial hEnergy
      (finiteEvenFourTorusZ2AugmentedTemporalField H Xg)
      (finiteEvenFourTorusZ2AugmentedTemporalField H Yg)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Xg) B
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Yg) B e
  have hH :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_abs_sub_le_energySpread
      H energyIdentity energyNontrivial hEnergy
      (finiteEvenFourTorusZ2AugmentedTemporalField H Yh)
      (finiteEvenFourTorusZ2AugmentedTemporalField H Xh)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Yh) B
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Xh) B e
  change
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Xg +
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Yh -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Yg -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Xh| ≤ _
  calc
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Xg +
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Yh -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Yg -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
          H energyIdentity energyNontrivial B e Xh| =
      |(finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Xg -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Yg) +
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Yh -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Xh)| := by
        congr 1
        ring
    _ ≤
      |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Xg -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Yg| +
        |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Yh -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e Xh| :=
      abs_add_le _ _
    _ ≤ (energyNontrivial - energyIdentity) +
        (energyNontrivial - energyIdentity) := by
      exact add_le_add hG hH
    _ = 2 * (energyNontrivial - energyIdentity) := by ring

/-- Crossing links whose exact support contains a temporal target vertex. -/
def finiteEvenFourTorusZ2TemporalTargetCrossingLinks
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H) :
    Finset (FiniteEvenFourTorusSpatialLink H) :=
  Finset.univ.filter fun e =>
    Sum.inl target ∈
      finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e

@[simp] theorem finiteEvenFourTorusZ2_mem_temporalTargetCrossingLinks
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    e ∈ finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target ↔
      Sum.inl target ∈
        finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e := by
  simp [finiteEvenFourTorusZ2TemporalTargetCrossingLinks]

/-- Exact augmented-coordinate neighborhood sharing at least one crossing link
with a temporal target. -/
def finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H) :
    Finset (FiniteEvenFourTorusZ2AugmentedCoordinate H) :=
  Finset.univ.filter fun source =>
    ∃ e : FiniteEvenFourTorusSpatialLink H,
      Sum.inl target ∈
          finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e ∧
        source ∈ finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e

@[simp] theorem finiteEvenFourTorusZ2_mem_temporalCrossingInteractionNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    source ∈
        finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood H target ↔
      ∃ e : FiniteEvenFourTorusSpatialLink H,
        Sum.inl target ∈
            finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e ∧
          source ∈ finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e := by
  simp [finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood]

/-- Only crossing links incident to the temporal target contribute to its
mixed crossing-action difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_eq_incident_sum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inl target) g h =
      ∑ e in finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e)
          X Y (Sum.inl target) g h := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_mixedDifference_eq_sum]
  classical
  calc
    (∑ e : FiniteEvenFourTorusSpatialLink H,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e)
          X Y (Sum.inl target) g h) =
      ∑ e : FiniteEvenFourTorusSpatialLink H,
        if Sum.inl target ∈
            finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e then
          finitePositiveWeightMixedActionDifference
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
              H energyIdentity energyNontrivial B e)
            X Y (Sum.inl target) g h
        else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hTarget : Sum.inl target ∈
          finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e
      · rw [if_pos hTarget]
      · rw [if_neg hTarget,
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_eq_zero_of_target_not_mem
            H energyIdentity energyNontrivial B e X Y
            (Sum.inl target) g h hTarget]
    _ = ∑ e in finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e)
          X Y (Sum.inl target) g h := by
      simp [finiteEvenFourTorusZ2TemporalTargetCrossingLinks]

/-- Outside the exact crossing interaction neighborhood, the temporal-target
mixed crossing-action difference vanishes. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_eq_zero_of_source_not_mem
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hSource : source ∉
      finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood H target)
    (hAgree : FiniteProductAgreeOff X Y source) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inl target) g h = 0 := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_eq_incident_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hTarget : Sum.inl target ∈
      finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e :=
    (finiteEvenFourTorusZ2_mem_temporalTargetCrossingLinks H target e).1 he
  have hSourceLink : source ∉
      finiteEvenFourTorusZ2AugmentedCrossingLinkSupport H e := by
    intro hMem
    apply hSource
    exact
      (finiteEvenFourTorusZ2_mem_temporalCrossingInteractionNeighborhood
        H target source).2 ⟨e, hTarget, hMem⟩
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_eq_zero_of_source_not_mem
      H energyIdentity energyNontrivial B e X Y
      (Sum.inl target) source g h hSourceLink hAgree

/-- The temporal-target mixed crossing-action oscillation is bounded by the
number of exactly incident crossing links times twice the two-level spread. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_abs_le_incidentCard
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (g h : Z2Gauge) :
    |finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inl target) g h| ≤
      2 *
        (finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target).card *
        (energyNontrivial - energyIdentity) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_eq_incident_sum]
  calc
    |∑ e in finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e)
          X Y (Sum.inl target) g h| ≤
      ∑ e in finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target,
        |finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy
            H energyIdentity energyNontrivial B e)
          X Y (Sum.inl target) g h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e in finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target,
        2 * (energyNontrivial - energyIdentity) := by
      apply Finset.sum_le_sum
      intro e _he
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingLinkEnergy_mixedDifference_abs_le_two_energySpread
          H energyIdentity energyNontrivial hEnergy B e X Y
          (Sum.inl target) g h
    _ = 2 *
        (finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target).card *
        (energyNontrivial - energyIdentity) := by
      simp
      ring

/-- For a temporal target, the spatial half-action cancels from the four-point
mixed difference, leaving exactly the encoded crossing action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_mixedDifference_eq_crossing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inl target) g h =
      finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inl target) g h := by
  unfold finitePositiveWeightMixedActionDifference
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
    finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction
  simp only [finiteEvenFourTorusZ2AugmentedLowerSlice_update_temporal]
  ring

/-- Exact temporal local mixed-action radius: zero outside the crossing
interaction neighborhood and the incident-cardinality bound inside. -/
def finiteEvenFourTorusZ2TemporalLocalMixedActionRadius
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  if source ∈
      finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood H target then
    2 *
      (finiteEvenFourTorusZ2TemporalTargetCrossingLinks H target).card *
      (energyNontrivial - energyIdentity)
  else 0

/-- The temporal local mixed-action radius is nonnegative. -/
theorem finiteEvenFourTorusZ2TemporalLocalMixedActionRadius_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ finiteEvenFourTorusZ2TemporalLocalMixedActionRadius
      H energyIdentity energyNontrivial target source := by
  unfold finiteEvenFourTorusZ2TemporalLocalMixedActionRadius
  split
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (sub_nonneg.mpr hEnergy)
  · exact le_rfl

/-- The actual temporal local row is now derived from the exact crossing
neighborhood and local two-level energy oscillation. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_mixedAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialVertex H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (_hNe : Sum.inl target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction
        H β energyIdentity energyNontrivial B)
      X Y (Sum.inl target)
      (finiteEvenFourTorusZ2TemporalLocalMixedActionRadius
        H energyIdentity energyNontrivial target source) := by
  intro g h
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalAction_temporal_mixedDifference_eq_crossing]
  by_cases hSource : source ∈
      finiteEvenFourTorusZ2TemporalCrossingInteractionNeighborhood H target
  · rw [finiteEvenFourTorusZ2TemporalLocalMixedActionRadius, if_pos hSource]
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_abs_le_incidentCard
        H β energyIdentity energyNontrivial hEnergy B X Y target g h
  · rw [
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedCrossingAction_temporal_mixedDifference_eq_zero_of_source_not_mem
        H β energyIdentity energyNontrivial B X Y target source g h
        hSource hAgree,
      abs_zero,
      finiteEvenFourTorusZ2TemporalLocalMixedActionRadius,
      if_neg hSource]

end

end MathlibAnalytic
end MGAP4D
