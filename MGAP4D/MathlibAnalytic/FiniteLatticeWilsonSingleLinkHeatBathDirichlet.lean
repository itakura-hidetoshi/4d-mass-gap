import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsRealVariance
import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Conditional expectation after exact heat-bath resampling of one link. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      f (L.replaceLink A e g)

/-- Conditional variance under exact single-link heat-bath resampling. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalVariance
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      (f (L.replaceLink A e g) -
        L.singleLinkConditionalExpectation f A e) ^ 2

/-- Every single-link conditional variance is nonnegative. -/
theorem finite_lattice_singleLinkConditionalVariance_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) :
    0 ≤ L.singleLinkConditionalVariance f A e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalVariance
  exact Finset.sum_nonneg fun g _hg =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

/-- Gibbs average of the conditional variance associated with one link. -/
def FiniteLatticeWilsonSystem.averagedSingleLinkVariance
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      L.singleLinkConditionalVariance f A e

/-- Averaged single-link conditional variance is nonnegative. -/
theorem finite_lattice_averagedSingleLinkVariance_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    0 ≤ L.averagedSingleLinkVariance f e := by
  classical
  unfold FiniteLatticeWilsonSystem.averagedSingleLinkVariance
  exact Finset.sum_nonneg fun A _hA =>
    mul_nonneg
      (finite_lattice_gibbsProbabilityReal_nonneg L A)
      (finite_lattice_singleLinkConditionalVariance_nonneg L f A e)

/-- Concrete heat-bath Dirichlet form obtained by summing exact conditional
variances over every lattice link. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathDirichletForm
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ e : L.Edge, L.averagedSingleLinkVariance f e

/-- The concrete single-link heat-bath Dirichlet form is nonnegative. -/
theorem finite_lattice_singleLinkHeatBathDirichletForm_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.singleLinkHeatBathDirichletForm f := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathDirichletForm
  exact Finset.sum_nonneg fun e _he =>
    finite_lattice_averagedSingleLinkVariance_nonneg L f e

/-- The concrete finite-volume spectral target: the public exact gap controls
Gibbs variance by the exact single-link Wilson heat-bath Dirichlet form. -/
def FiniteLatticeWilsonSystem.ExactGapSingleLinkHeatBathPoincare
    (L : FiniteLatticeWilsonSystem) : Prop :=
  ∀ f : L.Configuration → ℝ,
    exactGapValueReal * L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f

/-- Uniform concrete heat-bath Poincare target for a family of finite Wilson
systems. -/
def FiniteLatticeWilsonApproximationFamily.UniformExactGapSingleLinkHeatBathPoincare
    (F : FiniteLatticeWilsonApproximationFamily) : Prop :=
  ∀ i : F.index,
    (F.system i).ExactGapSingleLinkHeatBathPoincare

end

end MathlibAnalytic
end MGAP4D
