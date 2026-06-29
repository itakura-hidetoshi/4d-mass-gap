import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonLinkExchange

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite PMF has total real mass one. -/
theorem finite_oriented_pmf_sum_toReal_eq_one
    {alpha : Type*} [Fintype alpha]
    (p : PMF alpha) :
    ∑ a : alpha, (p a).toReal = 1 := by
  classical
  rw [← ENNReal.toReal_one]
  rw [← p.tsum_coe]
  rw [tsum_fintype]
  exact
    (ENNReal.toReal_sum
      (s := Finset.univ)
      (f := fun a : alpha => p a)
      (fun a _ha => p.apply_ne_top a)).symm

/-- A real observable is constant on fibers obtained by forgetting one
physical positive link. -/
def FiniteOrientedLatticeWilsonSystem.OffLinkFiberConstant
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) : Prop :=
  ∀ A B : L.Configuration,
    L.AgreeOffLink A B e → f A = f B

/-- Native conditional expectation viewed as an operator on observables. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => L.singleLinkConditionalExpectation f A e

/-- Native conditional expectation is invariant on each off-link fiber. -/
theorem finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalExpectation f A e =
      L.singleLinkConditionalExpectation f B e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
    L A B e hAgree]
  rw [finite_oriented_replaceLink_eq_of_agreeOffLink
    L A B e g hAgree]

/-- The native heat-bath projection produces an off-link-fiber-constant
observable. -/
theorem finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.OffLinkFiberConstant e
      (L.singleLinkHeatBathProjection e f) := by
  intro A B hAgree
  exact finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    L f A B e hAgree

/-- Native conditional expectation fixes every observable already constant on
the corresponding off-link fibers. -/
theorem finite_oriented_singleLinkHeatBathProjection_fixes
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ)
    (hFiber : L.OffLinkFiberConstant e f) :
    L.singleLinkHeatBathProjection e f = f := by
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  calc
    ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A e g).toReal *
          f (L.replaceLink A e g) =
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A e g).toReal * f A := by
      apply Finset.sum_congr rfl
      intro g _hg
      have hReplace : f (L.replaceLink A e g) = f A := by
        apply hFiber (L.replaceLink A e g) A
        intro e' he
        simp [FiniteOrientedLatticeWilsonSystem.replaceLink, he]
      rw [hReplace]
    _ = (∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A e g).toReal) * f A := by
      rw [Finset.sum_mul]
    _ = f A := by
      rw [finite_oriented_pmf_sum_toReal_eq_one]
      simp

/-- The native single-link heat-bath projection is idempotent. -/
theorem finite_oriented_singleLinkHeatBathProjection_idempotent
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) =
      L.singleLinkHeatBathProjection e f :=
  finite_oriented_singleLinkHeatBathProjection_fixes L e
    (L.singleLinkHeatBathProjection e f)
    (finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      L e f)

/-- Fixed points of the native heat-bath projection are exactly the observables
constant on off-link fibers. -/
theorem finite_oriented_singleLinkHeatBathProjection_fixed_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e f = f ↔
      L.OffLinkFiberConstant e f := by
  constructor
  · intro hFix
    rw [← hFix]
    exact finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      L e f
  · exact finite_oriented_singleLinkHeatBathProjection_fixes L e f

end

end MathlibAnalytic
end MGAP4D
