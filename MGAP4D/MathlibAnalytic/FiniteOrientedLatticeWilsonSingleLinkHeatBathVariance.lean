import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance
import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Native conditional expectation after exact resampling of one physical
positive link. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      f (L.replaceLink A e g)

/-- Native conditional variance under one physical-link heat-bath update. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalVariance
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      (f (L.replaceLink A e g) -
        L.singleLinkConditionalExpectation f A e) ^ 2

/-- Every native oriented single-link conditional variance is nonnegative. -/
theorem finite_oriented_singleLinkConditionalVariance_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    0 ≤ L.singleLinkConditionalVariance f A e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalVariance
  exact Finset.sum_nonneg fun g _hg =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

/-- Gibbs average of the native conditional variance for one physical link. -/
def FiniteOrientedLatticeWilsonSystem.averagedSingleLinkVariance
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      L.singleLinkConditionalVariance f A e

/-- Averaged native single-link variance is nonnegative. -/
theorem finite_oriented_averagedSingleLinkVariance_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    0 ≤ L.averagedSingleLinkVariance f e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.averagedSingleLinkVariance
  exact Finset.sum_nonneg fun A _hA =>
    mul_nonneg
      (finite_oriented_gibbsProbabilityReal_nonneg L A)
      (finite_oriented_singleLinkConditionalVariance_nonneg L f A e)

/-- Native physical-link heat-bath Dirichlet form. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathDirichletForm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ e : L.Edge, L.averagedSingleLinkVariance f e

/-- The native oriented heat-bath Dirichlet form is nonnegative. -/
theorem finite_oriented_singleLinkHeatBathDirichletForm_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.singleLinkHeatBathDirichletForm f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathDirichletForm
  exact Finset.sum_nonneg fun e _he =>
    finite_oriented_averagedSingleLinkVariance_nonneg L f e

/-- Native finite-volume Poincare target on physical positive links. -/
def FiniteOrientedLatticeWilsonSystem.ExactGapSingleLinkHeatBathPoincare
    (L : FiniteOrientedLatticeWilsonSystem) : Prop :=
  ∀ f : L.Configuration → ℝ,
    exactGapValueReal * L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f

end

end MathlibAnalytic
end MGAP4D
