import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsMeasure
import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Replace one link variable while leaving every other link unchanged. -/
def FiniteLatticeWilsonSystem.replaceLink
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.Configuration :=
  Function.update A e g

@[simp] theorem finite_lattice_replaceLink_same
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.replaceLink A e g e = g := by
  simp [FiniteLatticeWilsonSystem.replaceLink]

@[simp] theorem finite_lattice_replaceLink_ne
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e e' : L.Edge) (g : L.Gauge)
    (h : e' ≠ e) :
    L.replaceLink A e g e' = A e' := by
  simp [FiniteLatticeWilsonSystem.replaceLink, h]

/-- The conditional Boltzmann weight obtained by varying one link and freezing
all other links. -/
def FiniteLatticeWilsonSystem.singleLinkBoltzmannWeight
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) : ℝ≥0∞ :=
  L.boltzmannWeight (L.replaceLink A e g)

/-- Every single-link conditional Boltzmann weight is strictly positive. -/
theorem finite_lattice_singleLinkBoltzmannWeight_pos
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    0 < L.singleLinkBoltzmannWeight A e g :=
  finite_lattice_boltzmannWeight_pos L (L.replaceLink A e g)

/-- Single-link conditional partition function. -/
def FiniteLatticeWilsonSystem.singleLinkPartitionFunction
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) : ℝ≥0∞ :=
  ∑' g : L.Gauge, L.singleLinkBoltzmannWeight A e g

/-- The single-link conditional partition function is nonzero. -/
theorem finite_lattice_singleLinkPartitionFunction_ne_zero
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkPartitionFunction A e ≠ 0 := by
  intro hZero
  have hAll :
      ∀ g : L.Gauge, L.singleLinkBoltzmannWeight A e g = 0 :=
    ENNReal.tsum_eq_zero.mp hZero
  exact
    (ne_of_gt (finite_lattice_singleLinkBoltzmannWeight_pos L A e default))
      (hAll default)

/-- The single-link conditional partition function is finite. -/
theorem finite_lattice_singleLinkPartitionFunction_ne_top
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkPartitionFunction A e ≠ ∞ := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkPartitionFunction
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun g _hg => by
    simp [FiniteLatticeWilsonSystem.singleLinkBoltzmannWeight,
      FiniteLatticeWilsonSystem.boltzmannWeight]

/-- Exact single-link heat-bath conditional distribution for the Wilson Gibbs
measure.  It is constructed directly from the Wilson action rather than
postulated as a transition kernel. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalPMF
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) : PMF L.Gauge :=
  PMF.normalize (L.singleLinkBoltzmannWeight A e)
    (finite_lattice_singleLinkPartitionFunction_ne_zero L A e)
    (finite_lattice_singleLinkPartitionFunction_ne_top L A e)

/-- Pointwise formula for the single-link conditional Gibbs distribution. -/
theorem finite_lattice_singleLinkConditionalPMF_apply
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.singleLinkConditionalPMF A e g =
      L.singleLinkBoltzmannWeight A e g *
        (L.singleLinkPartitionFunction A e)⁻¹ := by
  rfl

/-- Real-valued finite Gibbs probability of a configuration. -/
def FiniteLatticeWilsonSystem.gibbsProbabilityReal
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  (L.gibbsPMF A).toReal

/-- Gibbs expectation of a real observable on finite link configurations. -/
def FiniteLatticeWilsonSystem.gibbsExpectationReal
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ :=
  ∑ A : L.Configuration, L.gibbsProbabilityReal A * f A

/-- Gibbs variance of a real observable. -/
def FiniteLatticeWilsonSystem.gibbsVarianceReal
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ :=
  ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      (f A - L.gibbsExpectationReal f) ^ 2

/-- Finite Wilson Gibbs variance is nonnegative. -/
theorem finite_lattice_gibbsVarianceReal_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsVarianceReal f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsVarianceReal
  exact Finset.sum_nonneg fun A _hA =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

/-- Conditional expectation after heat-bath resampling a single link. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) : ℝ :=
  ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A e g).toReal *
      f (L.replaceLink A e g)

/-- Conditional variance under exact single-link heat-bath resampling. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalVariance
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) : ℝ :=
  ∑ g : L.Gauge,
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
    (e : L.Edge) : ℝ :=
  ∑ A : L.Configuration,
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
    mul_nonneg ENNReal.toReal_nonneg
      (finite_lattice_singleLinkConditionalVariance_nonneg L f A e)

/-- Concrete heat-bath Dirichlet form obtained by summing exact conditional
variances over all lattice links. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathDirichletForm
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ :=
  ∑ e : L.Edge, L.averagedSingleLinkVariance f e

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
