import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathFluctuationSubspaces

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Native conditional expectation is unchanged by pre-updating the resampled
physical link. -/
theorem finite_oriented_singleLinkConditionalExpectation_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (h : L.Gauge) :
    L.singleLinkConditionalExpectation f (L.replaceLink A e h) e =
      L.singleLinkConditionalExpectation f A e := by
  apply finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
  intro e' he
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, he]

/-- On a resampled configuration, `Q_e f` is the value minus the conditional
expectation on the original off-link fiber. -/
theorem finite_oriented_singleLinkHeatBathFluctuation_replaceLink_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.singleLinkHeatBathFluctuationLinearMap e f
        (L.replaceLink A e g) =
      f (L.replaceLink A e g) -
        L.singleLinkConditionalExpectation f A e := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  change f (L.replaceLink A e g) -
      L.singleLinkConditionalExpectation f (L.replaceLink A e g) e =
    f (L.replaceLink A e g) -
      L.singleLinkConditionalExpectation f A e
  rw [finite_oriented_singleLinkConditionalExpectation_replaceLink]

/-- The local fluctuation has zero native conditional expectation. -/
theorem finite_oriented_singleLinkConditionalExpectation_fluctuation_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.singleLinkConditionalExpectation
        (L.singleLinkHeatBathFluctuationLinearMap e f) A e = 0 := by
  have h :=
    finite_oriented_singleLinkHeatBathProjection_annihilates_fluctuation
      L e f
  have hA := congrFun h A
  simpa
    [FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjectionLinearMap,
      FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection]
    using hA

/-- Conditional second moment of the native local fluctuation. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalFluctuationEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      (L.singleLinkHeatBathFluctuationLinearMap e f
        (L.replaceLink A e g)) ^ 2

/-- Native conditional variance is the conditional second moment of `Q_e f`. -/
theorem finite_oriented_singleLinkConditionalVariance_eq_fluctuationEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.singleLinkConditionalVariance f A e =
      L.singleLinkConditionalFluctuationEnergy f A e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalVariance
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalFluctuationEnergy
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_singleLinkHeatBathFluctuation_replaceLink_apply]

/-- Gibbs average of native local fluctuation energy at one physical link. -/
def FiniteOrientedLatticeWilsonSystem.averagedSingleLinkFluctuationEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      L.singleLinkConditionalFluctuationEnergy f A e

/-- Averaged conditional variance equals averaged native fluctuation energy. -/
theorem finite_oriented_averagedSingleLinkVariance_eq_fluctuationEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.averagedSingleLinkVariance f e =
      L.averagedSingleLinkFluctuationEnergy f e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.averagedSingleLinkVariance
    FiniteOrientedLatticeWilsonSystem.averagedSingleLinkFluctuationEnergy
  simp_rw [finite_oriented_singleLinkConditionalVariance_eq_fluctuationEnergy]

/-- Total native fluctuation Dirichlet form. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuationDirichletForm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ e : L.Edge,
    L.averagedSingleLinkFluctuationEnergy f e

/-- Native heat-bath Dirichlet form is exactly total local fluctuation energy. -/
theorem finite_oriented_singleLinkHeatBathDirichletForm_eq_fluctuationEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm f =
      L.singleLinkHeatBathFluctuationDirichletForm f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathDirichletForm
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuationDirichletForm
  apply Finset.sum_congr rfl
  intro e _he
  rw [finite_oriented_averagedSingleLinkVariance_eq_fluctuationEnergy]

end

end MathlibAnalytic
end MGAP4D
