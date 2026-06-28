import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditionalExpectation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- An orientation-correct observable is constant on fibers obtained by
forgetting one physical link. -/
def FiniteOrientedLatticeWilsonSystem.OffLinkFiberConstant
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) : Prop :=
  ∀ A B : L.Configuration,
    L.AgreeOffLink A B target → f A = f B

/-- Exact orientation-correct one-link heat-bath conditional expectation as an
operator on real observables. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => L.singleLinkConditionalExpectation f A target

/-- The oriented heat-bath projection produces an off-link fiber-constant
observable. -/
theorem finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) :
    L.OffLinkFiberConstant target
      (L.singleLinkHeatBathProjection target f) := by
  intro A B hAgree
  exact finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    L f A B target hAgree

/-- Exact oriented one-link conditional expectation fixes every observable
already constant on the corresponding off-link fibers. -/
theorem finite_oriented_singleLinkHeatBathProjection_fixes
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ)
    (hFiber : L.OffLinkFiberConstant target f) :
    L.singleLinkHeatBathProjection target f = f := by
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  calc
    ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal *
          f (L.replaceLink A target g) =
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal * f A := by
      apply Finset.sum_congr rfl
      intro g _hg
      have hReplace : f (L.replaceLink A target g) = f A := by
        apply hFiber (L.replaceLink A target g) A
        exact finite_oriented_agreeOffLink_replaceLink L A target g
      rw [hReplace]
    _ = (∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A target g).toReal) * f A := by
      rw [Finset.sum_mul]
    _ = f A := by
      rw [finite_pmf_sum_toReal_eq_one]
      simp

/-- The orientation-correct one-link heat-bath projection is idempotent. -/
theorem finite_oriented_singleLinkHeatBathProjection_idempotent
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection target
        (L.singleLinkHeatBathProjection target f) =
      L.singleLinkHeatBathProjection target f :=
  finite_oriented_singleLinkHeatBathProjection_fixes L target
    (L.singleLinkHeatBathProjection target f)
    (finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      L target f)

/-- Fixed points of the oriented one-link projection are exactly the
corresponding off-link fiber-constant observables. -/
theorem finite_oriented_singleLinkHeatBathProjection_fixed_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection target f = f ↔
      L.OffLinkFiberConstant target f := by
  constructor
  · intro hFix
    rw [← hFix]
    exact finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      L target f
  · exact finite_oriented_singleLinkHeatBathProjection_fixes L target f

end

end MathlibAnalytic
end MGAP4D
