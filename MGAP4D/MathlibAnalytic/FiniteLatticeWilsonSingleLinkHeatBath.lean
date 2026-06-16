import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsMeasure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Replace one link variable while leaving every other link unchanged. -/
def FiniteLatticeWilsonSystem.replaceLink
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.Configuration := by
  classical
  exact Function.update A e g

@[simp] theorem finite_lattice_replaceLink_same
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.replaceLink A e g e = g := by
  classical
  simp [FiniteLatticeWilsonSystem.replaceLink]

@[simp] theorem finite_lattice_replaceLink_ne
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e e' : L.Edge) (g : L.Gauge)
    (h : e' ≠ e) :
    L.replaceLink A e g e' = A e' := by
  classical
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
      ∀ g : L.Gauge, L.singleLinkBoltzmannWeight A e g = 0 := by
    simpa [FiniteLatticeWilsonSystem.singleLinkPartitionFunction] using
      (ENNReal.tsum_eq_zero.mp hZero)
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
measure. It is constructed directly from the Wilson action. -/
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

end

end MathlibAnalytic
end MGAP4D
