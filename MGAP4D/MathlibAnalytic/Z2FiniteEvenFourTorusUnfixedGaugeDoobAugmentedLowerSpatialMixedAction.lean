import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedTemporalUniformMixedActionRows
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialIncidenceBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The four lower-link augmented coordinates used by one spatial plaquette. -/
noncomputable def finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport
    (H : ℕ)
    (p : FiniteEvenFourTorusSpatialPlaquette H) :
    Finset (FiniteEvenFourTorusZ2AugmentedCoordinate H) :=
  Finset.univ.image fun k : Fin 4 =>
    Sum.inr (finiteEvenFourTorusSpatialPlaquetteBoundary H p k)

/-- One spatial plaquette energy as a function of the encoded augmented state. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2SpatialPlaquetteEnergy
    H energyIdentity energyNontrivial
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X) p

/-- Membership of a lower target in the augmented plaquette support is exactly
the existing spatial touching relation. -/
theorem finiteEvenFourTorusZ2_lower_mem_augmentedSpatialPlaquetteSupport_iff
    (H : ℕ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Sum.inr e ∈ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p ↔
      FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p e := by
  classical
  constructor
  · intro hMem
    rcases Finset.mem_image.mp hMem with ⟨k, _hk, hEq⟩
    exact ⟨k, Sum.inr.inj hEq⟩
  · rintro ⟨k, hk⟩
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_univ k, congrArg Sum.inr hk⟩

/-- The encoded spatial plaquette energy depends only on its exact four-link
lower support. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_eq_of_agree_support
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hAgree :
      ∀ coordinate ∈ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p,
        X coordinate = Y coordinate) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
        H energyIdentity energyNontrivial p X =
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
        H energyIdentity energyNontrivial p Y := by
  have hBoundary :
      ∀ k : Fin 4,
        finiteEvenFourTorusZ2AugmentedLowerSlice H X
            (finiteEvenFourTorusSpatialPlaquetteBoundary H p k) =
          finiteEvenFourTorusZ2AugmentedLowerSlice H Y
            (finiteEvenFourTorusSpatialPlaquetteBoundary H p k) := by
    intro k
    exact hAgree
      (Sum.inr (finiteEvenFourTorusSpatialPlaquetteBoundary H p k))
      (by
        classical
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
    finiteEvenFourTorusZ2SpatialPlaquetteEnergy
  rw [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_congr
    H (finiteEvenFourTorusZ2AugmentedLowerSlice H X)
    (finiteEvenFourTorusZ2AugmentedLowerSlice H Y) p hBoundary]

/-- Updating an augmented coordinate outside one plaquette support leaves that
local spatial energy unchanged exactly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_update_eq_of_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (coordinate : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g : Z2Gauge)
    (hNot : coordinate ∉ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
        H energyIdentity energyNontrivial p (Function.update X coordinate g) =
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
        H energyIdentity energyNontrivial p X := by
  apply
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_eq_of_agree_support
  intro other hOther
  by_cases hEq : other = coordinate
  · subst other
    exact (hNot hOther).elim
  · simp [Function.update, hEq]

/-- A local spatial-plaquette mixed difference is zero when the target is
outside the plaquette support. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_mixedDifference_eq_zero_of_target_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hTarget : target ∉ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p)
        X Y target g h = 0 := by
  unfold finitePositiveWeightMixedActionDifference
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial p X target g hTarget,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial p Y target h hTarget,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial p Y target g hTarget,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_update_eq_of_not_mem
      H energyIdentity energyNontrivial p X target h hTarget]
  ring

/-- If the environments differ only at a source outside one plaquette support,
that local plaquette has zero target/source mixed difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_mixedDifference_eq_zero_of_source_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hSource : source ∉ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p)
    (hAgree : FiniteProductAgreeOff X Y source) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p)
        X Y target g h = 0 := by
  have hEqG :
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p (Function.update X target g) =
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p (Function.update Y target g) := by
    apply
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_eq_of_agree_support
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
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p (Function.update Y target h) =
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p (Function.update X target h) := by
    apply
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_eq_of_agree_support
    intro coordinate hCoordinate
    by_cases hTarget : coordinate = target
    · subst coordinate
      simp
    · have hNeSource : coordinate ≠ source := by
        intro hEq
        subst coordinate
        exact hSource hCoordinate
      simp [Function.update, hTarget, hAgree coordinate hNeSource]
  unfold finitePositiveWeightMixedActionDifference
  rw [hEqG, hEqH]
  ring

/-- Every local two-level spatial plaquette energy has mixed oscillation at
most twice the energy spread. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_mixedDifference_abs_le_two_energySpread
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge) :
    |finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p)
        X Y target g h| ≤ 2 * (energyNontrivial - energyIdentity) := by
  let Xg := Function.update X target g
  let Yg := Function.update Y target g
  let Xh := Function.update X target h
  let Yh := Function.update Y target h
  have hG :=
    finiteEvenFourTorusZ2SpatialPlaquetteEnergy_abs_sub_le_energySpread
      H energyIdentity energyNontrivial hEnergy
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Xg)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Yg) p
  have hH :=
    finiteEvenFourTorusZ2SpatialPlaquetteEnergy_abs_sub_le_energySpread
      H energyIdentity energyNontrivial hEnergy
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Yh)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Xh) p
  change
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Xg +
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Yh -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Yg -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Xh| ≤ _
  calc
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Xg +
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Yh -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Yg -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Xh| =
      |(finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p Xg -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p Yg) +
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p Yh -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p Xh)| := by
        congr 1
        ring
    _ ≤
      |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Xg -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Yg| +
      |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Yh -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p Xh| := abs_add_le _ _
    _ ≤ (energyNontrivial - energyIdentity) +
        (energyNontrivial - energyIdentity) := add_le_add hG hH
    _ = 2 * (energyNontrivial - energyIdentity) := by ring

/-- The encoded lower spatial Wilson action. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X)

/-- The encoded spatial action is exactly the sum of encoded plaquette energies. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_eq_sum
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
        H energyIdentity energyNontrivial X =
      ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p X := by
  rfl

/-- Mixed differences commute exactly with the finite spatial plaquette sum. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_mixedDifference_eq_sum
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
          H energyIdentity energyNontrivial)
        X Y target g h =
      ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p)
          X Y target g h := by
  unfold finitePositiveWeightMixedActionDifference
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_eq_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]

/-- Exact augmented source neighborhood sharing a spatial plaquette with a
fixed lower-link target. -/
noncomputable def finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    Finset (FiniteEvenFourTorusZ2AugmentedCoordinate H) := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ p : FiniteEvenFourTorusSpatialPlaquette H,
      FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p target ∧
        source ∈ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p

@[simp] theorem finiteEvenFourTorusZ2_mem_lowerSpatialInteractionNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    source ∈ finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target ↔
      ∃ p : FiniteEvenFourTorusSpatialPlaquette H,
        FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p target ∧
          source ∈ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p := by
  classical
  simp [finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood]

/-- Only plaquettes touching the lower target contribute to its spatial mixed
difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_eq_touching_sum
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
          H energyIdentity energyNontrivial)
        X Y (Sum.inr target) g h =
      ∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H target,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p)
          X Y (Sum.inr target) g h := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_mixedDifference_eq_sum]
  classical
  calc
    (∑ p : FiniteEvenFourTorusSpatialPlaquette H,
      finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p)
        X Y (Sum.inr target) g h) =
      ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
        if FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p target then
          finitePositiveWeightMixedActionDifference
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
              H energyIdentity energyNontrivial p)
            X Y (Sum.inr target) g h
        else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hTouch : FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p target
      · rw [if_pos hTouch]
      · rw [if_neg hTouch,
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_mixedDifference_eq_zero_of_target_not_mem
            H energyIdentity energyNontrivial p X Y (Sum.inr target) g h]
        exact fun hMem => hTouch
          ((finiteEvenFourTorusZ2_lower_mem_augmentedSpatialPlaquetteSupport_iff
            H p target).1 hMem)
    _ = ∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H target,
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p)
          X Y (Sum.inr target) g h := by
      rw [finiteEvenFourTorusSpatialPlaquettesTouchingLink, Finset.sum_filter]

/-- Outside the exact shared-plaquette neighborhood, the lower-target spatial
mixed difference vanishes. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_eq_zero_of_source_not_mem
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge)
    (hSource : source ∉ finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target)
    (hAgree : FiniteProductAgreeOff X Y source) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
          H energyIdentity energyNontrivial)
        X Y (Sum.inr target) g h = 0 := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_eq_touching_sum]
  apply Finset.sum_eq_zero
  intro p hp
  have hTouch : FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p target :=
    (finiteEvenFourTorusSpatialPlaquette_mem_touchingLink_iff H target p).1 hp
  have hSourcePlaquette :
      source ∉ finiteEvenFourTorusZ2AugmentedSpatialPlaquetteSupport H p := by
    intro hMem
    apply hSource
    exact (finiteEvenFourTorusZ2_mem_lowerSpatialInteractionNeighborhood
      H target source).2 ⟨p, hTouch, hMem⟩
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_mixedDifference_eq_zero_of_source_not_mem
      H energyIdentity energyNontrivial p X Y (Sum.inr target) source
      g h hSourcePlaquette hAgree

/-- The lower-target spatial mixed difference is bounded by twice the target
plaquette incidence count times the energy spread. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_abs_le_touchingCard
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    |finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
          H energyIdentity energyNontrivial)
        X Y (Sum.inr target) g h| ≤
      2 * ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H target).card : ℝ) *
        (energyNontrivial - energyIdentity) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_eq_touching_sum]
  calc
    |∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H target,
      finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
          H energyIdentity energyNontrivial p)
        X Y (Sum.inr target) g h| ≤
      ∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H target,
        |finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy
            H energyIdentity energyNontrivial p)
          X Y (Sum.inr target) g h| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H target,
        2 * (energyNontrivial - energyIdentity) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedSpatialPlaquetteEnergy_mixedDifference_abs_le_two_energySpread
          H energyIdentity energyNontrivial hEnergy p X Y (Sum.inr target) g h
    _ = 2 * ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H target).card : ℝ) *
        (energyNontrivial - energyIdentity) := by
      simp [nsmul_eq_mul]
      ring

/-- The encoded lower spatial half-action. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  (1 / 2 : ℝ) *
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
      H energyIdentity energyNontrivial X

/-- Mixed differences of the spatial half-action are exactly half the full
spatial mixed differences. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction_mixedDifference_eq_half
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (g h : Z2Gauge) :
    finitePositiveWeightMixedActionDifference
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
          H energyIdentity energyNontrivial)
        X Y target g h =
      (1 / 2 : ℝ) *
        finitePositiveWeightMixedActionDifference
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction
            H energyIdentity energyNontrivial)
          X Y target g h := by
  unfold finitePositiveWeightMixedActionDifference
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
  ring

/-- Exact-support all-volume radius for the lower spatial half-action. -/
def finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  if source ∈ finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target then
    12 * (energyNontrivial - energyIdentity)
  else 0

/-- The lower spatial half-action radius is nonnegative. -/
theorem finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
      H energyIdentity energyNontrivial target source := by
  unfold finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
  split
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hEnergy)
  · exact le_rfl

/-- The actual lower spatial half-action has exact finite support and the
volume-independent radius `12 * energySpread`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction_uniform_mixedAction
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (_hNe : Sum.inr target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightMixedActionOscillationBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction
        H energyIdentity energyNontrivial)
      X Y (Sum.inr target)
      (finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
        H energyIdentity energyNontrivial target source) := by
  intro g h
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialHalfAction_mixedDifference_eq_half,
    abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  by_cases hSource : source ∈
      finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target
  · rw [finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius, if_pos hSource]
    have hLocal :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_abs_le_touchingCard
        H energyIdentity energyNontrivial hEnergy X Y target g h
    have hCardNat :=
      finiteEvenFourTorusSpatialPlaquettesTouchingLink_card_le_twelve H target
    have hCard :
        ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H target).card : ℝ) ≤ 12 := by
      exact_mod_cast hCardNat
    have hSpread : 0 ≤ energyNontrivial - energyIdentity := sub_nonneg.mpr hEnergy
    nlinarith
  · rw [
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedLowerSpatialAction_lower_mixedDifference_eq_zero_of_source_not_mem
        H energyIdentity energyNontrivial X Y target source g h hSource hAgree,
      abs_zero,
      mul_zero,
      finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius,
      if_neg hSource]

end

end MathlibAnalytic
end MGAP4D
