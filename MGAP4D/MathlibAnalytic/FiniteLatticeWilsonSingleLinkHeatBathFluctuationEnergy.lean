import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationProjection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- On a configuration obtained by resampling the selected link, the local
fluctuation is exactly the observable minus its single-link conditional
expectation at the original off-link fiber. -/
theorem finite_lattice_singleLinkHeatBathFluctuation_replaceLink_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.singleLinkHeatBathFluctuationLinearMap e f
        (L.replaceLink A e g) =
      f (L.replaceLink A e g) -
        L.singleLinkConditionalExpectation f A e := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply]
  change f (L.replaceLink A e g) -
      L.singleLinkConditionalExpectation f (L.replaceLink A e g) e =
    f (L.replaceLink A e g) -
      L.singleLinkConditionalExpectation f A e
  rw [finite_lattice_singleLinkConditionalExpectation_replaceLink]

/-- The local fluctuation has zero exact single-link conditional expectation. -/
theorem finite_lattice_singleLinkConditionalExpectation_fluctuation_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkConditionalExpectation
        (L.singleLinkHeatBathFluctuationLinearMap e f) A e = 0 := by
  have h :=
    finite_lattice_singleLinkHeatBathProjection_annihilates_fluctuation
      L e f
  have hA := congrFun h A
  simpa [FiniteLatticeWilsonSystem.singleLinkHeatBathProjectionLinearMap,
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection] using hA

/-- Conditional second moment of the local fluctuation along one exact
single-link heat-bath fiber. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalFluctuationEnergy
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      (L.singleLinkHeatBathFluctuationLinearMap e f
        (L.replaceLink A e g)) ^ 2

/-- Exact single-link conditional variance is the conditional second moment of
`Q_e f`. -/
theorem finite_lattice_singleLinkConditionalVariance_eq_fluctuationEnergy
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkConditionalVariance f A e =
      L.singleLinkConditionalFluctuationEnergy f A e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalVariance
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalFluctuationEnergy
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_lattice_singleLinkHeatBathFluctuation_replaceLink_apply]

/-- Gibbs average of the local fluctuation energy at one lattice link. -/
def FiniteLatticeWilsonSystem.averagedSingleLinkFluctuationEnergy
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      L.singleLinkConditionalFluctuationEnergy f A e

/-- The averaged conditional variance is the Gibbs-averaged local fluctuation
energy. -/
theorem finite_lattice_averagedSingleLinkVariance_eq_fluctuationEnergy
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.averagedSingleLinkVariance f e =
      L.averagedSingleLinkFluctuationEnergy f e := by
  classical
  unfold FiniteLatticeWilsonSystem.averagedSingleLinkVariance
  unfold FiniteLatticeWilsonSystem.averagedSingleLinkFluctuationEnergy
  apply Finset.sum_congr rfl
  intro A _hA
  rw [finite_lattice_singleLinkConditionalVariance_eq_fluctuationEnergy]

/-- The total finite Wilson heat-bath energy written as the sum of Gibbs-averaged
local fluctuation energies. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathFluctuationDirichletForm
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ e : L.Edge,
    L.averagedSingleLinkFluctuationEnergy f e

/-- The concrete heat-bath Dirichlet form is exactly the total local
fluctuation energy. -/
theorem finite_lattice_singleLinkHeatBathDirichletForm_eq_fluctuationEnergy
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm f =
      L.singleLinkHeatBathFluctuationDirichletForm f := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathDirichletForm
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathFluctuationDirichletForm
  apply Finset.sum_congr rfl
  intro e _he
  rw [finite_lattice_averagedSingleLinkVariance_eq_fluctuationEnergy]

/-- Total local fluctuation energy is nonnegative. -/
theorem finite_lattice_singleLinkHeatBathFluctuationDirichletForm_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.singleLinkHeatBathFluctuationDirichletForm f := by
  rw [← finite_lattice_singleLinkHeatBathDirichletForm_eq_fluctuationEnergy]
  exact finite_lattice_singleLinkHeatBathDirichletForm_nonneg L f

end

end MathlibAnalytic
end MGAP4D
