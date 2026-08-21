import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import Mathlib.Tactic

/-!
# Current one-link conditional projection laws

This file records the projection identities needed before iterating the current
compact-Haar Dobrushin conditional expectations.  It stays on the same current
carrier as `ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation`:
no historical heat-bath operator is reintroduced and no Gibbs covariance decay
claim is made here.

The exact one-link conditional expectation already depends only on the
configuration away from the resampled link.  We package the consequences used
by a finite resolvent construction:

* pre-replacing the target link does not change the conditional expectation;
* observables already constant on target-link fibers are fixed exactly;
* constants are fixed;
* averaging the projected value once more over the same conditional law is
  pointwise idempotent.

These are finite-volume kernel identities only.  In particular, they do not
identify update time with Euclidean time and do not assert global Gibbs
stationarity or covariance clustering.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Pre-replacing the resampled physical link leaves the current exact
conditional expectation unchanged. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalExpectationBCF O
        (C.base.replaceLink A target g) target =
      C.singleLinkConditionalExpectationBCF O A target := by
  apply
    continuous_compact_oriented_singleLinkConditionalExpectationBCF_eq_of_agreeOffLink
      C O (C.base.replaceLink A target g) A target
  intro e he
  exact compact_oriented_replaceLink_other C.base A target e g he

/-- The current exact one-link conditional expectation fixes every bounded
continuous observable already constant on fibers obtained by forgetting the
updated physical link. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_fixes_of_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge)
    (hFiber : ∀ A B : C.base.Configuration,
      C.base.AgreeOffLink A B target → O A = O B) :
    ∀ A : C.base.Configuration,
      C.singleLinkConditionalExpectationBCF O A target = O A := by
  intro A
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hPoint : ∀ g : C.base.Gauge,
      O (C.base.replaceLink A target g) = O A := by
    intro g
    apply hFiber (C.base.replaceLink A target g) A
    intro e he
    exact compact_oriented_replaceLink_other C.base A target e g he
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
  simp_rw [hPoint]
  simp

/-- In particular, the current exact compact one-link conditional expectation
fixes constants. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_const
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectationBCF
        (BoundedContinuousFunction.const _ c) A target = c := by
  apply
    continuous_compact_oriented_singleLinkConditionalExpectationBCF_fixes_of_offLinkFiberConstant
      C (BoundedContinuousFunction.const _ c) target
  intro B D hAgree
  rfl

/-- Kernel-level pointwise idempotence: after projecting onto the target-link
conditional law, averaging that projected value once more over the same fiber
leaves it unchanged. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_integral_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (∫ g : C.base.Gauge,
      C.singleLinkConditionalExpectationBCF O
        (C.base.replaceLink A target g) target
      ∂C.singleLinkConditionalMeasure A target) =
      C.singleLinkConditionalExpectationBCF O A target := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  simp_rw [continuous_compact_oriented_singleLinkConditionalExpectationBCF_replaceLink]
  simp

end

end MathlibAnalytic
end MGAP4D
