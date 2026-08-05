import MGAP4D.MathlibAnalytic.FinitePositiveWeightMultiplicativeFactorConditional
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedLocalTiltConditionalSource
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The encoded reduced one-slab factor before multiplication by the positive
lower-slice Perron ground. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
    Real.exp
      (-β *
        finiteEvenFourTorusZ2UnfixedGaugeReducedOneSlabAction
          H β energyIdentity energyNontrivial
          (finiteEvenFourTorusZ2AugmentedTemporalField H X)
          (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B)

/-- The encoded common lower-slice Perron factor. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ hEnergy
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X)

/-- The reduced encoded augmented weight factors exactly into its local
one-slab factor and the common lower Perron factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_product
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B =
      finitePositiveWeightProduct
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
          H β energyIdentity energyNontrivial B)
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
          H β energyIdentity energyNontrivial hβ hEnergy) := by
  rfl

/-- Strict positivity of the encoded reduced local factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
      H β energyIdentity energyNontrivial B X := by
  have hcardNat :
      0 < Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcardReal :
      0 < (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) := by
    exact_mod_cast hcardNat
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
  exact mul_pos (inv_pos.mpr hcardReal) (Real.exp_pos _)

/-- Strict positivity of the encoded Perron factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
      H β energyIdentity energyNontrivial hβ hEnergy X := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X)

/-- Updating a temporal coordinate leaves the decoded lower slice unchanged. -/
@[simp] theorem finiteEvenFourTorusZ2AugmentedLowerSlice_update_temporal
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (vertex : FiniteEvenFourTorusSpatialVertex H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2AugmentedLowerSlice H
        (Function.update X (Sum.inl vertex) g) =
      finiteEvenFourTorusZ2AugmentedLowerSlice H X := by
  funext link
  simp [finiteEvenFourTorusZ2AugmentedLowerSlice, Function.update]

/-- Updating a lower-link coordinate updates exactly that coordinate of the
decoded lower slice. -/
@[simp] theorem finiteEvenFourTorusZ2AugmentedLowerSlice_update_lower
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (link : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2AugmentedLowerSlice H
        (Function.update X (Sum.inr link) g) =
      Function.update
        (finiteEvenFourTorusZ2AugmentedLowerSlice H X) link g := by
  funext other
  by_cases hother : other = link
  · subst other
    simp [finiteEvenFourTorusZ2AugmentedLowerSlice, Function.update]
  · simp [finiteEvenFourTorusZ2AugmentedLowerSlice, Function.update, hother]

/-- Updating a lower-link coordinate leaves the temporal field unchanged. -/
@[simp] theorem finiteEvenFourTorusZ2AugmentedTemporalField_update_lower
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (link : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2AugmentedTemporalField H
        (Function.update X (Sum.inr link) g) =
      finiteEvenFourTorusZ2AugmentedTemporalField H X := by
  funext vertex
  simp [finiteEvenFourTorusZ2AugmentedTemporalField, Function.update]

/-- Updating a temporal coordinate updates exactly that coordinate of the
decoded temporal field. -/
@[simp] theorem finiteEvenFourTorusZ2AugmentedTemporalField_update_temporal
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (vertex : FiniteEvenFourTorusSpatialVertex H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2AugmentedTemporalField H
        (Function.update X (Sum.inl vertex) g) =
      Function.update
        (finiteEvenFourTorusZ2AugmentedTemporalField H X) vertex g := by
  funext other
  by_cases hother : other = vertex
  · subst other
    simp [finiteEvenFourTorusZ2AugmentedTemporalField, Function.update]
  · simp [finiteEvenFourTorusZ2AugmentedTemporalField, Function.update, hother]

/-- The Perron factor is exactly independent of every temporal coordinate
fiber. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_independent_temporal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (vertex : FiniteEvenFourTorusSpatialVertex H) :
    FiniteProductFunctionIndependentOfCoordinate
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      (Sum.inl vertex) := by
  intro X g
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
  rw [finiteEvenFourTorusZ2AugmentedLowerSlice_update_temporal]

/-- The full encoded reduced augmented temporal one-site conditional law is
exactly the conditional law of the local one-slab factor: the lower Perron
factor cancels from the fiber normalization. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_temporalConditionalProbability_eq_local
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (vertex : FiniteEvenFourTorusSpatialVertex H)
    (g : Z2Gauge) :
    finitePositiveWeightSingleSiteProbability
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy B)
        X (Sum.inl vertex) g =
      finitePositiveWeightSingleSiteProbability
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
          H β energyIdentity energyNontrivial B)
        X (Sum.inl vertex) g := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_product]
  exact
    finitePositiveWeightProduct_singleSiteProbability_eq_left
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_pos
        H β energyIdentity energyNontrivial B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_pos
        H β energyIdentity energyNontrivial hβ hEnergy)
      X (Sum.inl vertex)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_independent_temporal
        H β energyIdentity energyNontrivial hβ hEnergy vertex)
      g

/-- The same exact Perron cancellation holds for every temporal one-site
conditional expectation. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_temporalConditionalExpectation_eq_local
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (vertex : FiniteEvenFourTorusSpatialVertex H) :
    finitePositiveWeightSingleSiteExpectation
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy B)
        f X (Sum.inl vertex) =
      finitePositiveWeightSingleSiteExpectation
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
          H β energyIdentity energyNontrivial B)
        f X (Sum.inl vertex) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_product]
  exact
    finitePositiveWeightProduct_singleSiteExpectation_eq_left
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_pos
        H β energyIdentity energyNontrivial B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_pos
        H β energyIdentity energyNontrivial hβ hEnergy)
      f X (Sum.inl vertex)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_independent_temporal
        H β energyIdentity energyNontrivial hβ hEnergy vertex)

/-- Any temporal-target cross-ratio bound for the local one-slab factor
transfers unchanged to the full encoded reduced augmented weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_temporalCrossRatio_of_local
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (vertex : FiniteEvenFourTorusSpatialVertex H)
    (ratio : ℝ)
    (hRatio : 0 ≤ ratio)
    (hLocal :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inl vertex) ratio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      X Y (Sum.inl vertex) ratio := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_product]
  exact
    finitePositiveWeightProduct_singleSiteCrossRatioBound_of_rightIndependent
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      (fun Z => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_pos
          H β energyIdentity energyNontrivial B Z))
      (fun Z => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_pos
          H β energyIdentity energyNontrivial hβ hEnergy Z))
      X Y (Sum.inl vertex) ratio hRatio hLocal
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_independent_temporal
        H β energyIdentity energyNontrivial hβ hEnergy vertex)

/-- A lower-slice Perron-ground cross-ratio estimate lifts exactly to the
encoded Perron factor at the corresponding lower-link coordinate. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_lowerCrossRatio_of_slice
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (ratio : ℝ)
    (hPerron :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
          finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2AugmentedLowerSlice H X)
        (finiteEvenFourTorusZ2AugmentedLowerSlice H Y)
        target ratio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      X Y (Sum.inr target) ratio := by
  intro g h
  simpa [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor] using
    hPerron g h

/-- At a lower-link target, the full augmented cross-ratio separates into the
product of the local one-slab cross-ratio and the lower Perron-ground
cross-ratio.  This theorem isolates the only potentially nonlocal factor. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_lowerCrossRatio_of_local_mul_perron
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (localRatio perronRatio : ℝ)
    (hLocalRatio : 0 ≤ localRatio)
    (hPerronRatio : 0 ≤ perronRatio)
    (hLocal :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
          H β energyIdentity energyNontrivial B)
        X Y (Sum.inr target) localRatio)
    (hPerron :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
          finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2AugmentedLowerSlice H X)
        (finiteEvenFourTorusZ2AugmentedLowerSlice H Y)
        target perronRatio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      X Y (Sum.inr target) (localRatio * perronRatio) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_product]
  exact
    finitePositiveWeightProduct_singleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
        H β energyIdentity energyNontrivial B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor
        H β energyIdentity energyNontrivial hβ hEnergy)
      (fun Z => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor_pos
          H β energyIdentity energyNontrivial B Z))
      (fun Z => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_pos
          H β energyIdentity energyNontrivial hβ hEnergy Z))
      X Y (Sum.inr target) localRatio perronRatio
      hLocalRatio hPerronRatio hLocal
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedPerronFactor_lowerCrossRatio_of_slice
        H β energyIdentity energyNontrivial hβ hEnergy
        X Y target perronRatio hPerron)

end

end MathlibAnalytic
end MGAP4D
