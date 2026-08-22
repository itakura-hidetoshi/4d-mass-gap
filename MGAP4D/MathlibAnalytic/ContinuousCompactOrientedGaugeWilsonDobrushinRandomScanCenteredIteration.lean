import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceDirichlet
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredVariationFellerClosure
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
import Mathlib.Tactic

/-!
# Centered random-scan iteration on bounded continuous observables

The finite resolvent estimates already control the abstract variation iterates

`u₀ = v`, `uₘ₊₁ = U uₘ`.

This file ties those variation iterates back to the actual bounded-continuous
random-scan observable.  Compact Feller closure gives a BCF representative of
one random-scan step, while compact midpoint recentering restores a centered
variation profile with no loss in the declared linkwise variation constants.

Thus an observable together with its centered profile can be iterated as a
single state, and the profile variation after `m` random-scan steps is exactly
the previously defined variation-only iterate `U^m v`.

No covariance telescope, infinite Poisson solution, spatial decay conclusion,
continuum limit, or Hamiltonian mass-gap statement is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- One exact uniform random-scan Feller step is closed on the centered
variation carrier, with the sharp averaged Dobrushin variation profile. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.randomScanCenteredVariationProfile
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C
      (C.randomScanConditionalExpectationContinuousBCF O) := by
  let Q : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => C.randomScanConditionalExpectationContinuousBCF O A) := by
    simpa only [continuous_compact_oriented_randomScanConditionalExpectationContinuousBCF_apply]
      using P.randomScanVariationBound D
  exact Q.toCenteredVariationProfile

/-- Recentring the Feller random-scan observable does not change its declared
sharp Dobrushin variation profile. -/
@[simp] theorem continuous_compact_oriented_randomScanCenteredVariationProfile_variation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    (P.randomScanCenteredVariationProfile D).variation =
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
        D P.variation := by
  rfl

/-- An actual bounded-continuous observable packaged together with a centered
variation profile for that same observable. -/
structure ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState
    (C : ContinuousCompactOrientedGaugeWilsonSystem) where
  observable : BoundedContinuousFunction C.base.Configuration ℝ
  profile : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C observable

/-- Package an initial centered observable as a random-scan state. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.toRandomScanCenteredState
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O) :
    ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C :=
  { observable := O
    profile := P }

/-- One actual bounded-continuous random-scan step together with its recentered
sharp variation profile. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState.randomScanStep
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C :=
  { observable := C.randomScanConditionalExpectationContinuousBCF S.observable
    profile := S.profile.randomScanCenteredVariationProfile D }

/-- Finite iteration of the actual Feller random-scan observable and centered
variation profile. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState.randomScanIterate
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    ℕ → ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C :=
  fun m => Nat.rec S (fun _ previous => previous.randomScanStep D) m

@[simp] theorem continuous_compact_oriented_randomScanCenteredState_iterate_zero
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    S.randomScanIterate D 0 = S := by
  rfl

@[simp] theorem continuous_compact_oriented_randomScanCenteredState_iterate_succ
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (m : ℕ) :
    S.randomScanIterate D (m + 1) =
      (S.randomScanIterate D m).randomScanStep D := by
  rfl

/-- The actual observable component is literally iterated by the Feller
random-scan operator. -/
@[simp] theorem continuous_compact_oriented_randomScanCenteredState_iterate_succ_observable
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (m : ℕ) :
    (S.randomScanIterate D (m + 1)).observable =
      C.randomScanConditionalExpectationContinuousBCF
        (S.randomScanIterate D m).observable := by
  rfl

/-- The profile variation component is literally updated by the previously
proved random-scan Dobrushin variation operator. -/
@[simp] theorem continuous_compact_oriented_randomScanCenteredState_iterate_succ_variation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (m : ℕ) :
    (S.randomScanIterate D (m + 1)).profile.variation =
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
        D (S.randomScanIterate D m).profile.variation := by
  rfl

/-- Starting from a centered observable `P`, the variation profile carried by
the actual `m`-step Feller random-scan observable is exactly the abstract
variation-only iterate used by the finite resolvent estimates. -/
theorem continuous_compact_oriented_randomScanCenteredState_iterate_variation_eq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (m : ℕ) :
    ((P.toRandomScanCenteredState).randomScanIterate D m).profile.variation =
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
        D P.variation m := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
            D ((P.toRandomScanCenteredState).randomScanIterate D m).profile.variation =
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation D
            (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
              D P.variation m)
      exact congrArg
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation D)
        ih

end

end MathlibAnalytic
end MGAP4D
