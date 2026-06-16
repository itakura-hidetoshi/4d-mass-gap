import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite probability mass function has total extended-nonnegative mass one. -/
theorem finite_pmf_sum_eq_one
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, p a = 1 := by
  classical
  simpa only [tsum_fintype] using p.tsum_coe

/-- Passing a finite probability mass function to real masses commutes with the
finite total sum. -/
theorem finite_pmf_sum_toReal_eq_toReal_sum
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal =
      ENNReal.toReal (∑ a : α, p a) := by
  classical
  exact
    (ENNReal.toReal_sum
      (s := Finset.univ)
      (f := fun a : α => p a)
      (fun a _ha => p.apply_ne_top a)).symm

/-- A finite probability mass function has total real mass one. -/
theorem finite_pmf_sum_toReal_eq_one
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  rw [finite_pmf_sum_toReal_eq_toReal_sum p,
    finite_pmf_sum_eq_one p]
  simp

/-- A real observable is constant on the fibers obtained by forgetting one
selected link. -/
def FiniteLatticeWilsonSystem.OffLinkFiberConstant
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) : Prop :=
  ∀ A B : L.Configuration,
    L.AgreeOffLink A B e → f A = f B

/-- Exact single-link heat-bath conditional expectation, viewed as an operator
on real observables. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => L.singleLinkConditionalExpectation f A e

/-- The heat-bath projection always produces an observable that is constant on
off-link fibers. -/
theorem finite_lattice_singleLinkHeatBathProjection_offLinkFiberConstant
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.OffLinkFiberConstant e (L.singleLinkHeatBathProjection e f) := by
  intro A B hAgree
  exact finite_lattice_singleLinkConditionalExpectation_eq_of_agreeOffLink
    L f A B e hAgree

/-- Exact single-link conditional expectation fixes every observable that is
already constant on the corresponding off-link fibers. -/
theorem finite_lattice_singleLinkHeatBathProjection_fixes
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ)
    (hFiber : L.OffLinkFiberConstant e f) :
    L.singleLinkHeatBathProjection e f = f := by
  funext A
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
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
        simp [FiniteLatticeWilsonSystem.replaceLink, he]
      rw [hReplace]
    _ = (∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal) * f A := by
      rw [Finset.sum_mul]
    _ = f A := by
      rw [finite_pmf_sum_toReal_eq_one]
      simp

/-- Single-link heat-bath conditional expectation is idempotent. -/
theorem finite_lattice_singleLinkHeatBathProjection_idempotent
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) =
      L.singleLinkHeatBathProjection e f :=
  finite_lattice_singleLinkHeatBathProjection_fixes L e
    (L.singleLinkHeatBathProjection e f)
    (finite_lattice_singleLinkHeatBathProjection_offLinkFiberConstant L e f)

/-- A function is fixed by the single-link heat-bath projection exactly when it
is constant on the corresponding off-link fibers. -/
theorem finite_lattice_singleLinkHeatBathProjection_fixed_iff
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e f = f ↔
      L.OffLinkFiberConstant e f := by
  constructor
  · intro hFix
    rw [← hFix]
    exact finite_lattice_singleLinkHeatBathProjection_offLinkFiberConstant L e f
  · exact finite_lattice_singleLinkHeatBathProjection_fixes L e f

end

end MathlibAnalytic
end MGAP4D
