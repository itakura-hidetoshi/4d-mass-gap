import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonExponentTwoUnsignedProxyGibbs
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathVariance
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathVariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- For exponent-two groups, proxy and native conditional expectations agree. -/
theorem finite_oriented_unsignedProxy_singleLinkConditionalExpectation_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.unsignedProxy.singleLinkConditionalExpectation f A e =
      L.singleLinkConditionalExpectation f A e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_unsignedProxy_singleLinkConditionalPMF_eq
      L hInv A e,
    finite_oriented_unsignedProxy_replaceLink_eq L A e g]
  rfl

/-- For exponent-two groups, proxy and native one-link conditional variances
agree. -/
theorem finite_oriented_unsignedProxy_singleLinkConditionalVariance_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.unsignedProxy.singleLinkConditionalVariance f A e =
      L.singleLinkConditionalVariance f A e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalVariance
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalVariance
  rw [finite_oriented_unsignedProxy_singleLinkConditionalExpectation_eq
    L hInv f A e]
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_unsignedProxy_singleLinkConditionalPMF_eq
      L hInv A e,
    finite_oriented_unsignedProxy_replaceLink_eq L A e g]
  rfl

/-- For exponent-two groups, proxy and native averaged one-link variances
agree. -/
theorem finite_oriented_unsignedProxy_averagedSingleLinkVariance_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.unsignedProxy.averagedSingleLinkVariance f e =
      L.averagedSingleLinkVariance f e := by
  classical
  unfold FiniteLatticeWilsonSystem.averagedSingleLinkVariance
    FiniteOrientedLatticeWilsonSystem.averagedSingleLinkVariance
  apply Finset.sum_congr rfl
  intro A _hA
  rw [finite_oriented_unsignedProxy_gibbsProbabilityReal_eq L hInv A,
    finite_oriented_unsignedProxy_singleLinkConditionalVariance_eq
      L hInv f A e]

/-- For exponent-two groups, proxy and native physical-link heat-bath
Dirichlet forms agree. -/
theorem finite_oriented_unsignedProxy_singleLinkHeatBathDirichletForm_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (f : L.Configuration → ℝ) :
    L.unsignedProxy.singleLinkHeatBathDirichletForm f =
      L.singleLinkHeatBathDirichletForm f := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathDirichletForm
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathDirichletForm
  apply Finset.sum_congr rfl
  intro e _he
  rw [finite_oriented_unsignedProxy_averagedSingleLinkVariance_eq
    L hInv f e]

end

end MathlibAnalytic
end MGAP4D
