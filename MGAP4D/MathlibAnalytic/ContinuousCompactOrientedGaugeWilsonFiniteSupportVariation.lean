import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredVariationFellerClosure
import Mathlib.Tactic

/-!
# Finite-support variation profiles for compact Wilson observables

The spatial covariance estimate is formulated in terms of proof-relevant
linkwise variation profiles.  Local cylinder observables, however, are often
available first through a simpler support statement: changing links outside a
finite set does not change the observable.

For a bounded continuous real observable depending only on a finite support
`S`, this file constructs the canonical coarse variation profile

`delta_e(O) = 2 * ‖O‖` for `e ∈ S`, and `0` otherwise.

No Dobrushin threshold, covariance estimate, continuum limit, or physical mass
gap is used here.  This is only the support-to-variation bridge needed to feed
finite-support observables into the existing covariance-clustering carrier.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A bounded continuous observable which depends only on a finite set of
physical links admits a link-variation bound supported on exactly that set,
with the universal coarse oscillation constant `2 * ‖O‖`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : Finset C.base.geometry.Edge)
    (hSupport : ∀ A B : C.base.Configuration,
      (∀ e, e ∈ S → A e = B e) → O A = O B) :
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound C (fun A => O A) := by
  classical
  refine
    { variation := fun e => if e ∈ S then 2 * ‖O‖ else 0
      variation_nonneg := ?_
      variation_bound := ?_ }
  · intro e
    by_cases he : e ∈ S
    · simp only [he, if_true]
      positivity
    · simp [he]
  · intro e A B hAgree
    by_cases he : e ∈ S
    · simp only [he, if_true]
      rw [← Real.norm_eq_abs]
      calc
        ‖O A - O B‖ ≤ ‖O A‖ + ‖O B‖ := norm_sub_le _ _
        _ ≤ ‖O‖ + ‖O‖ :=
          add_le_add (O.norm_coe_le_norm A) (O.norm_coe_le_norm B)
        _ = 2 * ‖O‖ := by ring
    · have hEq : O A = O B := by
        apply hSupport A B
        intro source hsource
        apply hAgree source
        intro hSource
        subst source
        exact he hsource
      simp [he, hEq]

/-- On the declared finite support, the coarse variation profile is exactly
the universal oscillation bound `2 * ‖O‖`. -/
theorem continuous_compact_oriented_ofFiniteSupport_variation_eq_two_mul_norm_of_mem
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : Finset C.base.geometry.Edge)
    (hSupport : ∀ A B : C.base.Configuration,
      (∀ e, e ∈ S → A e = B e) → O A = O B)
    {e : C.base.geometry.Edge}
    (he : e ∈ S) :
    (ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
      O S hSupport).variation e = 2 * ‖O‖ := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport, he]

/-- The finite-support variation profile vanishes identically away from the
declared support. -/
theorem continuous_compact_oriented_ofFiniteSupport_variation_eq_zero_of_not_mem
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : Finset C.base.geometry.Edge)
    (hSupport : ∀ A B : C.base.Configuration,
      (∀ e, e ∈ S → A e = B e) → O A = O B)
    {e : C.base.geometry.Edge}
    (he : e ∉ S) :
    (ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
      O S hSupport).variation e = 0 := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport, he]

/-- Compact midpoint recentering upgrades the same finite-support variation
bound to the centered profile required by the random-scan covariance route. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.ofFiniteSupport
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : Finset C.base.geometry.Edge)
    (hSupport : ∀ A B : C.base.Configuration,
      (∀ e, e ∈ S → A e = B e) → O A = O B) :
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O :=
  (ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
    O S hSupport).toCenteredVariationProfile

/-- Midpoint recentering preserves the coarse finite-support variation on the
support exactly. -/
theorem continuous_compact_oriented_centeredOfFiniteSupport_variation_eq_two_mul_norm_of_mem
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : Finset C.base.geometry.Edge)
    (hSupport : ∀ A B : C.base.Configuration,
      (∀ e, e ∈ S → A e = B e) → O A = O B)
    {e : C.base.geometry.Edge}
    (he : e ∈ S) :
    (ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.ofFiniteSupport
      O S hSupport).variation e = 2 * ‖O‖ := by
  classical
  change (ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
    O S hSupport).variation e = 2 * ‖O‖
  exact continuous_compact_oriented_ofFiniteSupport_variation_eq_two_mul_norm_of_mem
    O S hSupport he

/-- The centered finite-support profile has no variation outside its declared
support. -/
theorem continuous_compact_oriented_centeredOfFiniteSupport_variation_eq_zero_of_not_mem
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : Finset C.base.geometry.Edge)
    (hSupport : ∀ A B : C.base.Configuration,
      (∀ e, e ∈ S → A e = B e) → O A = O B)
    {e : C.base.geometry.Edge}
    (he : e ∉ S) :
    (ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.ofFiniteSupport
      O S hSupport).variation e = 0 := by
  classical
  change (ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
    O S hSupport).variation e = 0
  exact continuous_compact_oriented_ofFiniteSupport_variation_eq_zero_of_not_mem
    O S hSupport he

end

end MathlibAnalytic
end MGAP4D
