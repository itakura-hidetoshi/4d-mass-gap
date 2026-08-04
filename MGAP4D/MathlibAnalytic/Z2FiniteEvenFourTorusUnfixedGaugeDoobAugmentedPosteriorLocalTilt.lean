import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosteriorBoundaryRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The part of the one-slab action that depends on the augmented state
`(U,A)` at fixed upper boundary `B`.  The upper spatial half-action is omitted
because it is constant over the augmented state space and therefore cancels
exactly in the normalized posterior. -/
def finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A +
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
      H β energyIdentity energyNontrivial U A B

/-- Exact separation of the upper-boundary-only spatial half-action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_reduced_add_upper
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H β energyIdentity energyNontrivial U A B =
      finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
          H β energyIdentity energyNontrivial U A B +
        (1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
    finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
  ring

/-- Unnormalized augmented posterior weight after removing the upper spatial
half-action. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
      Real.exp (-β *
        finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
          H β energyIdentity energyNontrivial U A B) *
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- The reduced augmented weight is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
      H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  have hcardNat :
      0 < Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcardReal :
      0 < (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) := by
    exact_mod_cast hcardNat
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
  exact mul_pos
    (mul_pos (inv_pos.mpr hcardReal) (Real.exp_pos _))
    (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
      H β energyIdentity energyNontrivial hβ hEnergy A)

/-- The original augmented weight is an upper-boundary scalar times the
reduced weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_eq_upperFactor_mul_reduced
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy U A B =
      Real.exp
          (-β * ((1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial B)) *
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_reduced_add_upper]
  rw [show
    -β *
        (finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
            H β energyIdentity energyNontrivial U A B +
          (1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial B) =
      -β * ((1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial B) +
        -β *
          finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
            H β energyIdentity energyNontrivial U A B by ring]
  rw [Real.exp_add]
  ring

/-- Reduced augmented posterior normalizer. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
    ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy U A B

/-- The reduced normalizer is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
      H β energyIdentity energyNontrivial hβ hEnergy B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
  apply Finset.sum_pos
  · intro A _hA
    apply Finset.sum_pos
    · intro U _hU
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_pos
          H β energyIdentity energyNontrivial hβ hEnergy U A B
    · exact ⟨1, Finset.mem_univ _⟩
  · exact ⟨1, Finset.mem_univ _⟩

/-- The original normalizer contains exactly the same upper-boundary scalar. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_eq_upperFactor_mul_reduced
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
        H β energyIdentity energyNontrivial hβ hEnergy B =
      Real.exp
          (-β * ((1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial B)) *
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_eq_sum_augmentedWeight]
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_eq_upperFactor_mul_reduced]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [Finset.mul_sum]

/-- Exact cancellation of the upper spatial half-action in the normalized
augmented posterior. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_eq_reduced
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy U A B =
      finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy U A B /
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_eq_upperFactor_mul_reduced,
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_eq_upperFactor_mul_reduced]
  have hUpper :
      Real.exp
          (-β * ((1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial B)) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  field_simp [hUpper]

/-- Agreement of two augmented states on the three coordinates touched by one
upper-boundary source link: the lower source link and the two temporal links at
its endpoints. -/
def FiniteEvenFourTorusZ2AugmentedAgreeAtBoundarySource
    {H : ℕ}
    (source : FiniteEvenFourTorusSpatialLink H)
    (U V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H) : Prop :=
  U source.1 = V source.1 ∧
    U (finiteEvenFourTorusSpatialVertexStep H source.1 source.2) =
      V (finiteEvenFourTorusSpatialVertexStep H source.1 source.2) ∧
    A source = C source

/-- The source temporal plaquette holonomy depends only on those three
augmented coordinates. -/
theorem finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_of_augmentedAgreeAtBoundarySource
    (H : ℕ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (U V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A C B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree :
      FiniteEvenFourTorusZ2AugmentedAgreeAtBoundarySource source U V A C) :
    finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B source =
      finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H V C B source := by
  rcases hAgree with ⟨hTail, hHead, hLower⟩
  unfold finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
  rw [hTail, hHead, hLower]

/-- The corresponding local crossing energy has the same locality. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_eq_of_augmentedAgreeAtBoundarySource
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (U V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A C B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree :
      FiniteEvenFourTorusZ2AugmentedAgreeAtBoundarySource source U V A C) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
        H energyIdentity energyNontrivial U A B source =
      finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
        H energyIdentity energyNontrivial V C B source := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy
  rw [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_of_augmentedAgreeAtBoundarySource
    H source U V A C B hAgree]

/-- Exact local Radon--Nikodym tilt generated by replacing one upper-boundary
link.  The upper spatial half-action is absent because it has already cancelled
from the normalized posterior. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  Real.exp
    (-β *
      (finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H β energyIdentity energyNontrivial U A B -
        finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
          H β energyIdentity energyNontrivial U A
          (finiteZ2GaugeReplaceCoordinate B source g)))

/-- The local tilt is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
      H β energyIdentity energyNontrivial source g U A B := by
  exact Real.exp_pos _

/-- The boundary tilt is supported exactly on the lower source link and the two
temporal links at its endpoints. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_eq_of_agree
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A C B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree :
      FiniteEvenFourTorusZ2AugmentedAgreeAtBoundarySource source U V A C) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g U A B =
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g V C B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_eq_linkEnergy_sub
      H β energyIdentity energyNontrivial U A B source g,
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_eq_linkEnergy_sub
      H β energyIdentity energyNontrivial V C B source g]
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_eq_of_augmentedAgreeAtBoundarySource
      H energyIdentity energyNontrivial source U V A C B hAgree,
    finiteEvenFourTorusZ2UnfixedGaugeCrossingLinkEnergy_eq_of_augmentedAgreeAtBoundarySource
      H energyIdentity energyNontrivial source U V A C
      (finiteZ2GaugeReplaceCoordinate B source g) hAgree]

/-- Exact one-source tilt identity for the reduced unnormalized weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_eq_localTilt_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy U A B =
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
          H β energyIdentity energyNontrivial source g U A B *
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy U A
          (finiteZ2GaugeReplaceCoordinate B source g) := by
  let lowerAction :=
    (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A
  let crossing :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
      H β energyIdentity energyNontrivial U A B
  let crossing' :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
      H β energyIdentity energyNontrivial U A
      (finiteZ2GaugeReplaceCoordinate B source g)
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
    finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
  change
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          Real.exp (-β * (lowerAction + crossing)) *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A =
      Real.exp (-β * (crossing - crossing')) *
        ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          Real.exp (-β * (lowerAction + crossing')) *
          finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy A)
  rw [show -β * (lowerAction + crossing) =
      -β * (crossing - crossing') + -β * (lowerAction + crossing') by ring]
  rw [Real.exp_add]
  ring

/-- Exact normalizer tilt identity. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_eq_sum_localTilt_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
        H β energyIdentity energyNontrivial hβ hEnergy B =
      ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
              H β energyIdentity energyNontrivial source g U A B *
            finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
              H β energyIdentity energyNontrivial hβ hEnergy U A
              (finiteZ2GaugeReplaceCoordinate B source g) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
  apply Finset.sum_congr rfl
  intro A _hA
  apply Finset.sum_congr rfl
  intro U _hU
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_eq_localTilt_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy source g U A B

/-- The local tilt is bounded below by the one-crossing Boltzmann factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_lower
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Real.exp (-β * (energyNontrivial - energyIdentity)) ≤
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g U A B := by
  let difference :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A B -
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A
        (finiteZ2GaugeReplaceCoordinate B source g)
  have hDifference :
      |difference| ≤ energyNontrivial - energyIdentity := by
    simpa [difference] using
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_abs_le_energySpread
        H β energyIdentity energyNontrivial hEnergy U A B source g
  have hUpper := (abs_le.mp hDifference).2
  have hExponent :
      -β * (energyNontrivial - energyIdentity) ≤ -β * difference := by
    nlinarith
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
  change Real.exp (-β * (energyNontrivial - energyIdentity)) ≤
    Real.exp (-β * difference)
  exact Real.exp_monotone hExponent

/-- The local tilt is bounded above by the reciprocal one-crossing Boltzmann
factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_upper
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g U A B ≤
      Real.exp (β * (energyNontrivial - energyIdentity)) := by
  let difference :=
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A B -
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A
        (finiteZ2GaugeReplaceCoordinate B source g)
  have hDifference :
      |difference| ≤ energyNontrivial - energyIdentity := by
    simpa [difference] using
      finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_sub_replace_abs_le_energySpread
        H β energyIdentity energyNontrivial hEnergy U A B source g
  have hLower := (abs_le.mp hDifference).1
  have hExponent : -β * difference ≤ β * (energyNontrivial - energyIdentity) := by
    nlinarith
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
  change Real.exp (-β * difference) ≤
    Real.exp (β * (energyNontrivial - energyIdentity))
  exact Real.exp_monotone hExponent

/-- Posterior expectation of the local source tilt under the replaced upper
boundary. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
    ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ hEnergy U A
          (finiteZ2GaugeReplaceCoordinate B source g) *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
          H β energyIdentity energyNontrivial source g U A B

/-- The local tilt normalizer is exactly the ratio of the two reduced
normalizers. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer_eq_reduced_ratio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer
        H β energyIdentity energyNontrivial hβ hEnergy source g B =
      finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy B /
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_eq_reduced]
  calc
    (∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        (finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy U A
            (finiteZ2GaugeReplaceCoordinate B source g) /
          finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteZ2GaugeReplaceCoordinate B source g)) *
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
            H β energyIdentity energyNontrivial source g U A B) =
        ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
                H β energyIdentity energyNontrivial source g U A B *
              finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy U A
                (finiteZ2GaugeReplaceCoordinate B source g)) /
              finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g) := by
      apply Finset.sum_congr rfl
      intro A _hA
      apply Finset.sum_congr rfl
      intro U _hU
      ring
    _ = ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
                H β energyIdentity energyNontrivial source g U A B *
              finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy U A
                (finiteZ2GaugeReplaceCoordinate B source g)) /
            finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
              H β energyIdentity energyNontrivial hβ hEnergy
              (finiteZ2GaugeReplaceCoordinate B source g) := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [← Finset.sum_div]
    _ = (∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
                H β energyIdentity energyNontrivial source g U A B *
              finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy U A
                (finiteZ2GaugeReplaceCoordinate B source g)) /
            finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
              H β energyIdentity energyNontrivial hβ hEnergy
              (finiteZ2GaugeReplaceCoordinate B source g) := by
      rw [← Finset.sum_div]
    _ = finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy B /
        finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) := by
      rw [← finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_eq_sum_localTilt_mul_replace]

/-- The local tilt normalizer is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer
      H β energyIdentity energyNontrivial hβ hEnergy source g B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer_eq_reduced_ratio]
  exact div_pos
    (finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_pos
      H β energyIdentity energyNontrivial hβ hEnergy B)
    (finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_pos
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate B source g))

/-- Exact local-tilt representation of the normalized augmented posterior. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_eq_localTilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy U A B =
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
          H β energyIdentity energyNontrivial source g U A B /
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy source g B) *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ hEnergy U A
          (finiteZ2GaugeReplaceCoordinate B source g) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_eq_reduced,
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_eq_reduced,
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_eq_localTilt_mul_replace,
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTiltNormalizer_eq_reduced_ratio]
  have hLeft :
      finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy B ≠ 0 :=
    ne_of_gt
      (finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_pos
        H β energyIdentity energyNontrivial hβ hEnergy B)
  have hRight :
      finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) ≠ 0 :=
    ne_of_gt
      (finiteEvenFourTorusZ2UnfixedGaugeDoobReducedPosteriorNormalizer_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g))
  field_simp [hLeft, hRight]
  ring

end

end MathlibAnalytic
end MGAP4D
