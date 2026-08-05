import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialIncidenceBound
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosterior
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The local two-valued crossing energy attached to one spatial link in the
augmented one-slab state. -/
def finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1 then
    energyIdentity
  else
    energyNontrivial

/-- The existing crossing action is exactly the finite sum of its local link
energies. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_sum_linkEnergy
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A B =
      ∑ e : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
          H energyIdentity energyNontrivial U A B e := by
  simp [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction,
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy]

/-- Replacing a different upper-boundary link leaves a local crossing
holonomy unchanged. -/
theorem finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_replace_eq_of_ne
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e i : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (hie : i ≠ e) :
    finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
        H U A (finiteZ2GaugeReplaceCoordinate B e g) i =
      finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B i := by
  unfold finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
  rw [finiteZ2GaugeReplaceCoordinate_noteq B e i g hie]

/-- Hence a different upper-boundary replacement leaves the corresponding
local crossing energy unchanged. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_replace_eq_of_ne
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e i : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (hie : i ≠ e) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
        H energyIdentity energyNontrivial U A
        (finiteZ2GaugeReplaceCoordinate B e g) i =
      finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
        H energyIdentity energyNontrivial U A B i := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
  rw [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_replace_eq_of_ne
    H U A B e i g hie]

/-- Every local crossing-energy difference is bounded by the two-level energy
spread. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_abs_sub_le_energySpread
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B C D : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    |finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
          H energyIdentity energyNontrivial U A B e -
        finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
          H energyIdentity energyNontrivial V C D e| ≤
      energyNontrivial - energyIdentity := by
  have hLeft :
      energyIdentity ≤
          finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
            H energyIdentity energyNontrivial U A B e ∧
        finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
            H energyIdentity energyNontrivial U A B e ≤ energyNontrivial := by
    unfold finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
    split <;> simp [hEnergy]
  have hRight :
      energyIdentity ≤
          finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
            H energyIdentity energyNontrivial V C D e ∧
        finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
            H energyIdentity energyNontrivial V C D e ≤ energyNontrivial := by
    unfold finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
    split <;> simp [hEnergy]
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- A one-link replacement of the upper boundary changes exactly one crossing
energy term. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_eq_linkEnergy_sub
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H β energyIdentity energyNontrivial U A B -
        finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H β energyIdentity energyNontrivial U A
          (finiteZ2GaugeReplaceCoordinate B e g) =
      finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
          H energyIdentity energyNontrivial U A B e -
        finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
          H energyIdentity energyNontrivial U A
          (finiteZ2GaugeReplaceCoordinate B e g) e := by
  classical
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_sum_linkEnergy,
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_sum_linkEnergy,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single e]
  · intro i _hi hie
    rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_replace_eq_of_ne
      H energyIdentity energyNontrivial U A B e i g hie]
    ring
  · simp

/-- The crossing part of the augmented action has a dimension-free one-source
oscillation bound. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_abs_le_energySpread
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    |finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H β energyIdentity energyNontrivial U A B -
        finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H β energyIdentity energyNontrivial U A
          (finiteZ2GaugeReplaceCoordinate B e g)| ≤
      energyNontrivial - energyIdentity := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_eq_linkEnergy_sub]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_abs_sub_le_energySpread
      H energyIdentity energyNontrivial hEnergy U U A B A
      (finiteZ2GaugeReplaceCoordinate B e g) e

/-- The all-volume twelve-occurrence spatial incidence bound gives a uniform
upper-boundary spatial-action oscillation. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_abs_le_twelve
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    |finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial B -
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate B e g)| ≤
      12 * (energyNontrivial - energyIdentity) := by
  have hLocal :=
    finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_abs_le_touchingCard
      H energyIdentity energyNontrivial hEnergy B e g
  have hCardNat :=
    finiteEvenFourTorusSpatialPlaquettesTouchingLink_card_le_twelve H e
  have hCard :
      ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) ≤ 12 := by
    exact_mod_cast hCardNat
  exact hLocal.trans
    (mul_le_mul_of_nonneg_right hCard (sub_nonneg.mpr hEnergy))

/-- The full augmented one-slab action changes by at most seven local energy
spreads under one upper-boundary link replacement: one crossing term plus one
spatial half-action with at most twelve boundary occurrences. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_sub_replace_abs_le_seven
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    |finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
          H β energyIdentity energyNontrivial U A B -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
          H β energyIdentity energyNontrivial U A
          (finiteZ2GaugeReplaceCoordinate B e g)| ≤
      7 * (energyNontrivial - energyIdentity) := by
  let crossingDifference :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A B -
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A
        (finiteZ2GaugeReplaceCoordinate B e g)
  let spatialDifference :=
    finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial B -
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial
        (finiteZ2GaugeReplaceCoordinate B e g)
  have hCrossing :
      |crossingDifference| ≤ energyNontrivial - energyIdentity := by
    simpa [crossingDifference] using
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_abs_le_energySpread
        H β energyIdentity energyNontrivial hEnergy U A B e g
  have hSpatial :
      |spatialDifference| ≤ 12 * (energyNontrivial - energyIdentity) := by
    simpa [spatialDifference] using
      finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_abs_le_twelve
        H energyIdentity energyNontrivial hEnergy B e g
  have hDecomposition :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
            H β energyIdentity energyNontrivial U A B -
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
            H β energyIdentity energyNontrivial U A
            (finiteZ2GaugeReplaceCoordinate B e g) =
        crossingDifference + (1 / 2 : ℝ) * spatialDifference := by
    simp [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction,
      crossingDifference, spatialDifference]
    ring
  rw [hDecomposition]
  calc
    |crossingDifference + (1 / 2 : ℝ) * spatialDifference| ≤
        |crossingDifference| + |(1 / 2 : ℝ) * spatialDifference| :=
      abs_add_le _ _
    _ = |crossingDifference| + (1 / 2 : ℝ) * |spatialDifference| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (energyNontrivial - energyIdentity) +
        (1 / 2 : ℝ) * (12 * (energyNontrivial - energyIdentity)) := by
      exact add_le_add hCrossing
        (mul_le_mul_of_nonneg_left hSpatial (by norm_num))
    _ = 7 * (energyNontrivial - energyIdentity) := by ring

/-- Explicit mutual one-source likelihood-ratio factor for the actual
augmented posterior. -/
def z2UnfixedGaugeDoobAugmentedBoundaryRatio
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  Real.exp (7 * β * (energyNontrivial - energyIdentity))

/-- The boundary-ratio factor is strictly positive. -/
theorem z2UnfixedGaugeDoobAugmentedBoundaryRatio_pos
    (β energyIdentity energyNontrivial : ℝ) :
    0 < z2UnfixedGaugeDoobAugmentedBoundaryRatio
      β energyIdentity energyNontrivial := by
  exact Real.exp_pos _

/-- The unnormalized augmented posterior weight has a volume-independent
one-source likelihood-ratio bound. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_le_boundaryRatio_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy U A B ≤
      z2UnfixedGaugeDoobAugmentedBoundaryRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy U A
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  let S := finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
    H β energyIdentity energyNontrivial U A B
  let S' := finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
    H β energyIdentity energyNontrivial U A
      (finiteZ2GaugeReplaceCoordinate B e g)
  let spread := energyNontrivial - energyIdentity
  have hAction : |S - S'| ≤ 7 * spread := by
    simpa [S, S', spread] using
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_sub_replace_abs_le_seven
        H β energyIdentity energyNontrivial hEnergy U A B e g
  have hDifference : S' - S ≤ 7 * spread := by
    have hLower := (abs_le.mp hAction).1
    linarith
  have hScaled := mul_le_mul_of_nonneg_left hDifference hβ
  have hExponent : -β * S ≤ 7 * β * spread + (-β * S') := by
    nlinarith
  have hExp :
      Real.exp (-β * S) ≤
        Real.exp (7 * β * spread) * Real.exp (-β * S') := by
    rw [← Real.exp_add]
    exact Real.exp_monotone hExponent
  have hGround :
      0 ≤ finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy A :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ hEnergy A)
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
    z2UnfixedGaugeDoobAugmentedBoundaryRatio
  change
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          Real.exp (-β * S) *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A ≤ _
  calc
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          Real.exp (-β * S) *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A ≤
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          (Real.exp (7 * β * spread) * Real.exp (-β * S')) *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hExp (by positivity)) hGround
    _ = Real.exp (7 * β * spread) *
        ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          Real.exp (-β * S') *
          finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy A) := by ring

/-- The unnormalized augmented likelihood-ratio estimate is two-sided. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_replace_le_boundaryRatio_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy U A
        (finiteZ2GaugeReplaceCoordinate B e g) ≤
      z2UnfixedGaugeDoobAugmentedBoundaryRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_le_boundaryRatio_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy U A
      (finiteZ2GaugeReplaceCoordinate B e g) e (B e)
  simpa [finiteZ2GaugeReplaceCoordinate_restore] using h

/-- The posterior normalizer is the total augmented unnormalized mass. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_eq_sum_augmentedWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
        H β energyIdentity energyNontrivial hβ hEnergy B =
      ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
  apply Finset.sum_congr rfl
  intro A _hA
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_sum_temporal
      H β energyIdentity energyNontrivial hβ hEnergy A B).symm

/-- Summation preserves the same one-source ratio for the augmented posterior
normalizer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_le_boundaryRatio_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
        H β energyIdentity energyNontrivial hβ hEnergy B ≤
      z2UnfixedGaugeDoobAugmentedBoundaryRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_eq_sum_augmentedWeight,
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_eq_sum_augmentedWeight,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _hA
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U _hU
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_le_boundaryRatio_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy U A B e g

/-- The normalizer likelihood-ratio estimate is two-sided. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_replace_le_boundaryRatio_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B e g) ≤
      z2UnfixedGaugeDoobAugmentedBoundaryRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy B := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_le_boundaryRatio_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate B e g) e (B e)
  simpa [finiteZ2GaugeReplaceCoordinate_restore] using h

/-- After normalization, one upper-boundary link replacement changes every
augmented posterior atom by at most the square of the unnormalized ratio. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_le_boundaryRatio_sq_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy U A B ≤
      (z2UnfixedGaugeDoobAugmentedBoundaryRatio
          β energyIdentity energyNontrivial) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ hEnergy U A
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  let R := z2UnfixedGaugeDoobAugmentedBoundaryRatio
    β energyIdentity energyNontrivial
  let W := finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
    H β energyIdentity energyNontrivial hβ hEnergy U A B
  let W' := finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
    H β energyIdentity energyNontrivial hβ hEnergy U A
      (finiteZ2GaugeReplaceCoordinate B e g)
  let Z := finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
    H β energyIdentity energyNontrivial hβ hEnergy B
  let Z' := finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
    H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate B e g)
  have hR0 : 0 ≤ R :=
    le_of_lt
      (z2UnfixedGaugeDoobAugmentedBoundaryRatio_pos
        β energyIdentity energyNontrivial)
  have hW : W ≤ R * W' := by
    simpa [W, W', R] using
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_le_boundaryRatio_mul_replace
        H β energyIdentity energyNontrivial hβ hEnergy U A B e g
  have hW'0 : 0 ≤ W' := by
    exact finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy U A
      (finiteZ2GaugeReplaceCoordinate B e g)
  have hZpos : 0 < Z := by
    simpa [Z] using
      finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_pos
        H β energyIdentity energyNontrivial hβ hEnergy B
  have hZ'pos : 0 < Z' := by
    simpa [Z'] using
      finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B e g)
  have hZreverse : Z' ≤ R * Z := by
    simpa [Z, Z', R] using
      finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_replace_le_boundaryRatio_mul
        H β energyIdentity energyNontrivial hβ hEnergy B e g
  have hInverse : Z⁻¹ ≤ R * Z'⁻¹ := by
    have hDiv : 1 / Z ≤ R / Z' := by
      rw [div_le_div_iff₀ hZpos hZ'pos]
      simpa using hZreverse
    simpa [one_div, div_eq_mul_inv] using hDiv
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
  change W / Z ≤ R ^ 2 * (W' / Z')
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    W * Z⁻¹ ≤ (R * W') * Z⁻¹ :=
      mul_le_mul_of_nonneg_right hW (inv_nonneg.mpr hZpos.le)
    _ = R * W' * Z⁻¹ := by ring
    _ ≤ R * W' * (R * Z'⁻¹) :=
      mul_le_mul_of_nonneg_left hInverse (mul_nonneg hR0 hW'0)
    _ = R ^ 2 * (W' * Z'⁻¹) := by ring

/-- The normalized augmented posterior likelihood-ratio estimate is also
mutual. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_replace_le_boundaryRatio_sq_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy U A
        (finiteZ2GaugeReplaceCoordinate B e g) ≤
      (z2UnfixedGaugeDoobAugmentedBoundaryRatio
          β energyIdentity energyNontrivial) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_le_boundaryRatio_sq_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy U A
      (finiteZ2GaugeReplaceCoordinate B e g) e (B e)
  simpa [finiteZ2GaugeReplaceCoordinate_restore] using h

end

end MathlibAnalytic
end MGAP4D
