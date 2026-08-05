import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalCrossRatioInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The signed four-point mixed difference of an action across one target
fiber and two surrounding environments. -/
def finitePositiveWeightMixedActionDifference
    {ι G : Type}
    [DecidableEq ι]
    (action : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (g h : G) : ℝ :=
  action (Function.update A target g) +
    action (Function.update B target h) -
    action (Function.update B target g) -
    action (Function.update A target h)

/-- A uniform absolute mixed-action oscillation bound along one target fiber. -/
def FinitePositiveWeightMixedActionOscillationBound
    {ι G : Type}
    [DecidableEq ι]
    (action : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (radius : ℝ) : Prop :=
  ∀ g h : G,
    |finitePositiveWeightMixedActionDifference action A B target g h| ≤ radius

/-- The reversed mixed difference is controlled by the same absolute
oscillation radius. -/
theorem finitePositiveWeight_neg_mixedActionDifference_le
    {ι G : Type}
    [DecidableEq ι]
    (action : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (radius : ℝ)
    (hMixed : FinitePositiveWeightMixedActionOscillationBound
      action A B target radius)
    (g h : G) :
    -finitePositiveWeightMixedActionDifference action A B target g h ≤ radius := by
  exact le_trans (neg_le_abs _) (hMixed g h)

/-- A mixed-action oscillation bound gives the exact four-point cross-ratio
bound for the positive exponential weight `exp (-β action)`. -/
theorem finitePositiveExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (action : (ι → G) → ℝ)
    (β : ℝ)
    (hβ : 0 ≤ β)
    (A B : ι → G)
    (target : ι)
    (radius : ℝ)
    (hMixed : FinitePositiveWeightMixedActionOscillationBound
      action A B target radius) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (fun X : ι → G => Real.exp (-β * action X))
      A B target (Real.exp (β * radius)) := by
  intro g h
  have hDifference :
      -finitePositiveWeightMixedActionDifference action A B target g h ≤ radius :=
    finitePositiveWeight_neg_mixedActionDifference_le
      action A B target radius hMixed g h
  have hScaled := mul_le_mul_of_nonneg_left hDifference hβ
  have hExponent :
      -β * action (Function.update A target g) +
          -β * action (Function.update B target h) ≤
        β * radius +
          (-β * action (Function.update B target g) +
            -β * action (Function.update A target h)) := by
    unfold finitePositiveWeightMixedActionDifference at hScaled
    nlinarith
  calc
    Real.exp (-β * action (Function.update A target g)) *
        Real.exp (-β * action (Function.update B target h)) =
      Real.exp
        (-β * action (Function.update A target g) +
          -β * action (Function.update B target h)) := by
        rw [Real.exp_add]
    _ ≤ Real.exp
        (β * radius +
          (-β * action (Function.update B target g) +
            -β * action (Function.update A target h))) :=
      Real.exp_le_exp.mpr hExponent
    _ = Real.exp (β * radius) *
        (Real.exp (-β * action (Function.update B target g)) *
          Real.exp (-β * action (Function.update A target h))) := by
      simp only [Real.exp_add]

/-- A common scalar prefactor cancels from the four-point comparison.  No
positivity hypothesis on the scalar is needed because it appears as a square. -/
theorem finitePositiveScaledExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (action : (ι → G) → ℝ)
    (scale β : ℝ)
    (hβ : 0 ≤ β)
    (A B : ι → G)
    (target : ι)
    (radius : ℝ)
    (hMixed : FinitePositiveWeightMixedActionOscillationBound
      action A B target radius) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (fun X : ι → G => scale * Real.exp (-β * action X))
      A B target (Real.exp (β * radius)) := by
  have hExponential :=
    finitePositiveExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
      action β hβ A B target radius hMixed
  intro g h
  have hPoint := hExponential g h
  calc
    (scale * Real.exp (-β * action (Function.update A target g))) *
        (scale * Real.exp (-β * action (Function.update B target h))) =
      scale ^ 2 *
        (Real.exp (-β * action (Function.update A target g)) *
          Real.exp (-β * action (Function.update B target h))) := by
      ring
    _ ≤ scale ^ 2 *
        (Real.exp (β * radius) *
          (Real.exp (-β * action (Function.update B target g)) *
            Real.exp (-β * action (Function.update A target h)))) :=
      mul_le_mul_of_nonneg_left hPoint (sq_nonneg scale)
    _ = Real.exp (β * radius) *
        ((scale * Real.exp (-β * action (Function.update B target g))) *
          (scale * Real.exp (-β * action (Function.update A target h)))) := by
      ring

/-- Rowwise mixed-action radii for a positive exponential product weight.
This is the reusable interface between local action geometry and the generic
cross-ratio/Dobrushin layer. -/
structure FinitePositiveExponentialWeightMixedActionRows
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (action : (ι → G) → ℝ) where
  radius : ι → ι → ℝ
  radius_nonneg : ∀ target source, 0 ≤ radius target source
  mixedActionBound :
    ∀ (target source : ι) (A B : ι → G),
      target ≠ source →
      FiniteProductAgreeOff A B source →
        FinitePositiveWeightMixedActionOscillationBound
          action A B target (radius target source)

namespace FinitePositiveExponentialWeightMixedActionRows

variable
  {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  {action : (ι → G) → ℝ}

/-- Rowwise mixed-action data immediately supplies the cross-ratio estimate
for any common scalar multiple of `exp (-β action)`. -/
theorem scaledExponentialCrossRatioBound
    (D : FinitePositiveExponentialWeightMixedActionRows action)
    (scale β : ℝ)
    (hβ : 0 ≤ β)
    (target source : ι)
    (A B : ι → G)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A B source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (fun X : ι → G => scale * Real.exp (-β * action X))
      A B target (Real.exp (β * D.radius target source)) := by
  exact
    finitePositiveScaledExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
      action scale β hβ A B target (D.radius target source)
      (D.mixedActionBound target source A B hNe hAgree)

end FinitePositiveExponentialWeightMixedActionRows

end

end MathlibAnalytic
end MGAP4D
