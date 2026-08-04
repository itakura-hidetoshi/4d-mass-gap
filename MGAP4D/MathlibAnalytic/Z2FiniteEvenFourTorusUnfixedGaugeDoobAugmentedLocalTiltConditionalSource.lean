import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosteriorLocalTilt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A single coordinate type for the augmented state `(U,A)`: temporal links
are indexed by spatial vertices and lower-slice links by spatial links. -/
abbrev FiniteEvenFourTorusZ2AugmentedCoordinate (H : ℕ) :=
  Sum (FiniteEvenFourTorusSpatialVertex H)
    (FiniteEvenFourTorusSpatialLink H)

/-- Product representation of an augmented temporal/lower-slice state. -/
abbrev FiniteEvenFourTorusZ2AugmentedConfiguration (H : ℕ) :=
  FiniteEvenFourTorusZ2AugmentedCoordinate H → Z2Gauge

/-- Encode a temporal-link field and lower slice as one finite product state. -/
def finiteEvenFourTorusZ2EncodeAugmentedConfiguration
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteEvenFourTorusZ2AugmentedConfiguration H
  | Sum.inl vertex => U vertex
  | Sum.inr link => A link

/-- Recover the temporal-link field from an encoded augmented state. -/
def finiteEvenFourTorusZ2AugmentedTemporalField
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    FiniteEvenFourTorusZ2TemporalLinkField H :=
  fun vertex => X (Sum.inl vertex)

/-- Recover the lower slice from an encoded augmented state. -/
def finiteEvenFourTorusZ2AugmentedLowerSlice
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    FiniteEvenFourTorusZ2SliceConfiguration H :=
  fun link => X (Sum.inr link)

@[simp]
theorem finiteEvenFourTorusZ2AugmentedTemporalField_encode
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2AugmentedTemporalField H
        (finiteEvenFourTorusZ2EncodeAugmentedConfiguration H U A) = U := by
  rfl

@[simp]
theorem finiteEvenFourTorusZ2AugmentedLowerSlice_encode
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2AugmentedLowerSlice H
        (finiteEvenFourTorusZ2EncodeAugmentedConfiguration H U A) = A := by
  rfl

@[simp]
theorem finiteEvenFourTorusZ2EncodeAugmentedConfiguration_decode
    (H : ℕ)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finiteEvenFourTorusZ2EncodeAugmentedConfiguration H
        (finiteEvenFourTorusZ2AugmentedTemporalField H X)
        (finiteEvenFourTorusZ2AugmentedLowerSlice H X) = X := by
  funext coordinate
  cases coordinate <;> rfl

/-- The exact three-coordinate support of an upper-boundary source-link tilt:
the lower source link and the temporal links at its two endpoints. -/
def finiteEvenFourTorusZ2AugmentedBoundarySourceSupport
    (H : ℕ)
    (source : FiniteEvenFourTorusSpatialLink H) :
    Finset (FiniteEvenFourTorusZ2AugmentedCoordinate H) :=
  {Sum.inr source,
    Sum.inl source.1,
    Sum.inl
      (finiteEvenFourTorusSpatialVertexStep H source.1 source.2)}

/-- The reduced augmented weight viewed as a positive weight on one finite
product configuration space. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight
    H β energyIdentity energyNontrivial hβ hEnergy
    (finiteEvenFourTorusZ2AugmentedTemporalField H X)
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- The actual one-source boundary tilt viewed as a function on the encoded
augmented product state. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt
    H β energyIdentity energyNontrivial source g
    (finiteEvenFourTorusZ2AugmentedTemporalField H X)
    (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Positivity of the encoded reduced augmented weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
      H β energyIdentity energyNontrivial hβ hEnergy B X := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_pos
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2AugmentedTemporalField H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Positivity of the encoded local tilt. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
      H β energyIdentity energyNontrivial source g B X := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_pos
      H β energyIdentity energyNontrivial source g
      (finiteEvenFourTorusZ2AugmentedTemporalField H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Exact multiplicative-tilt identity after encoding the augmented state. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_tilt_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B X =
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
          H β energyIdentity energyNontrivial source g B X *
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) X := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobReducedAugmentedWeight_eq_localTilt_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy source g
      (finiteEvenFourTorusZ2AugmentedTemporalField H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Functional form of the exact multiplicative-tilt identity. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_multiplicativeTilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B =
      finitePositiveWeightMultiplicativeTilt
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g))
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
          H β energyIdentity energyNontrivial source g B) := by
  funext X
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_tilt_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy source g B X

/-- The encoded local tilt is supported on exactly the declared three
coordinates. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_supported
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteProductFunctionSupportedOn
      (finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g B) := by
  intro X Y hAgree
  apply
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_eq_of_agree
  refine ⟨?_, ?_, ?_⟩
  · exact hAgree (Sum.inl source.1) (by
      simp [finiteEvenFourTorusZ2AugmentedBoundarySourceSupport])
  · exact hAgree
      (Sum.inl
        (finiteEvenFourTorusSpatialVertexStep H source.1 source.2))
      (by simp [finiteEvenFourTorusZ2AugmentedBoundarySourceSupport])
  · exact hAgree (Sum.inr source) (by
      simp [finiteEvenFourTorusZ2AugmentedBoundarySourceSupport])

/-- Lower pointwise bound for the encoded actual local tilt. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_lower
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    Real.exp (-β * (energyNontrivial - energyIdentity)) ≤
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g B X := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_lower
      H β energyIdentity energyNontrivial hβ hEnergy source g
      (finiteEvenFourTorusZ2AugmentedTemporalField H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Upper pointwise bound for the encoded actual local tilt. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_upper
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt
        H β energyIdentity energyNontrivial source g B X ≤
      Real.exp (β * (energyNontrivial - energyIdentity)) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryLocalTilt_upper
      H β energyIdentity energyNontrivial hβ hEnergy source g
      (finiteEvenFourTorusZ2AugmentedTemporalField H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X) B

/-- Generic finite-support source estimate specialized to the actual encoded
augmented posterior weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_genericSourceBound
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    finitePositiveWeightSingleSiteConditionalCrossL1
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy B)
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g))
        X target ≤
      finitePositiveWeightLocalTiltConditionalSourceBound
        (finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source)
        (Real.exp (-β * (energyNontrivial - energyIdentity)))
        (Real.exp (β * (energyNontrivial - energyIdentity)))
        target := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_eq_multiplicativeTilt
    H β energyIdentity energyNontrivial hβ hEnergy source g B]
  apply
    finitePositiveWeightMultiplicativeTilt_singleSiteConditionalCrossL1_le_sourceBound
  · intro Y
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g) Y
  · intro Y
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_pos
        H β energyIdentity energyNontrivial source g B Y
  · exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_supported
        H β energyIdentity energyNontrivial source g B
  · exact Real.exp_pos _
  · exact Real.exp_pos _
  · apply Real.exp_monotone
    have hDelta : 0 ≤ energyNontrivial - energyIdentity :=
      sub_nonneg.mpr hEnergy
    nlinarith
  · intro Y
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_lower
        H β energyIdentity energyNontrivial hβ hEnergy source g B Y
  · intro Y
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryLocalTilt_upper
        H β energyIdentity energyNontrivial hβ hEnergy source g B Y

/-- The inverse conditional tilt ratio simplifies to the explicit two-crossing
exponential factor. -/
theorem z2UnfixedGaugeDoobBoundaryLocalTiltRatio_inv_eq_exp_neg_two
    (β energyIdentity energyNontrivial : ℝ) :
    (Real.exp (β * (energyNontrivial - energyIdentity)) /
        Real.exp (-β * (energyNontrivial - energyIdentity)))⁻¹ =
      Real.exp (-2 * β * (energyNontrivial - energyIdentity)) := by
  rw [← Real.exp_sub]
  rw [← Real.exp_neg]
  congr 1
  ring

/-- Explicit actual source vector on the encoded augmented coordinate space. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  if target ∈
      finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source then
    2 *
      (1 - Real.exp
        (-2 * β * (energyNontrivial - energyIdentity)))
  else 0

/-- The generic local-tilt source bound is exactly the explicit actual source
vector. -/
theorem finitePositiveWeightLocalTiltConditionalSourceBound_eq_z2AugmentedBoundary
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    finitePositiveWeightLocalTiltConditionalSourceBound
        (finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source)
        (Real.exp (-β * (energyNontrivial - energyIdentity)))
        (Real.exp (β * (energyNontrivial - energyIdentity)))
        target =
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source target := by
  unfold finitePositiveWeightLocalTiltConditionalSourceBound
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
  by_cases htarget :
      target ∈ finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source
  · simp only [htarget, if_true]
    rw [z2UnfixedGaugeDoobBoundaryLocalTiltRatio_inv_eq_exp_neg_two]
  · simp [htarget]

/-- Actual finite-support source estimate: the one-site conditional discrepancy
is zero away from the three source coordinates and is bounded by
`2 * (1 - exp(-2 * beta * DeltaE))` on them. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    finitePositiveWeightSingleSiteConditionalCrossL1
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy B)
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g))
        X target ≤
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source target := by
  rw [← finitePositiveWeightLocalTiltConditionalSourceBound_eq_z2AugmentedBoundary]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_genericSourceBound
      H β energyIdentity energyNontrivial hβ hEnergy source g B X target

/-- Every lower-link one-site conditional away from the source link is
unchanged exactly by the upper-boundary source replacement. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_lower_eq_zero_of_ne
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source target : FiniteEvenFourTorusSpatialLink H)
    (htarget : target ≠ source)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finitePositiveWeightSingleSiteConditionalCrossL1
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy B)
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g))
        X (Sum.inr target) = 0 := by
  have hUpper :=
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
      H β energyIdentity energyNontrivial hβ hEnergy source g B X
      (Sum.inr target)
  have hNotMem :
      Sum.inr target ∉
        finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source := by
    simp [finiteEvenFourTorusZ2AugmentedBoundarySourceSupport, htarget]
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound,
    if_neg hNotMem] at hUpper
  exact le_antisymm hUpper
    (finitePositiveWeightSingleSiteConditionalCrossL1_nonneg
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g))
      X (Sum.inr target))

/-- At the lower source coordinate, the explicit source amplitude is the
one-crossing conditional likelihood-ratio bound. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_lower_source_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    finitePositiveWeightSingleSiteConditionalCrossL1
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy B)
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g))
        X (Sum.inr source) ≤
      2 *
        (1 - Real.exp
          (-2 * β * (energyNontrivial - energyIdentity))) := by
  simpa [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound,
    finiteEvenFourTorusZ2AugmentedBoundarySourceSupport] using
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
      H β energyIdentity energyNontrivial hβ hEnergy source g B X
      (Sum.inr source)

end

end MathlibAnalytic
end MGAP4D