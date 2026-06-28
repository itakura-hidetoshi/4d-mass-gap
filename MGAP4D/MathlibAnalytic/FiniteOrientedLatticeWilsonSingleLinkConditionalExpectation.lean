import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact conditional expectation obtained by resampling one physical link with
the orientation-correct Wilson conditional law. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A target g).toReal *
      f (L.replaceLink A target g)

/-- Pointwise expansion of the oriented one-link conditional expectation. -/
theorem finite_oriented_singleLinkConditionalExpectation_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkConditionalExpectation f A target =
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal *
          f (L.replaceLink A target g) := by
  rfl

/-- The oriented conditional expectation is constant on every off-target
configuration fiber. -/
theorem finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalExpectation f A target =
      L.singleLinkConditionalExpectation f B target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B target hAgree,
    finite_oriented_replaceLink_eq_of_agreeOffLink
      L A B target g hAgree]

/-- Pre-updating the resampled physical link does not change its exact
conditional expectation. -/
theorem finite_oriented_singleLinkConditionalExpectation_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.singleLinkConditionalExpectation f
        (L.replaceLink A target g) target =
      L.singleLinkConditionalExpectation f A target := by
  apply finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
  intro e he
  exact finite_oriented_replaceLink_of_ne L A target e g he

/-- The exact one-link heat-bath operator on real observables. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathOperator
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => L.singleLinkConditionalExpectation f A target

end

end MathlibAnalytic
end MGAP4D
