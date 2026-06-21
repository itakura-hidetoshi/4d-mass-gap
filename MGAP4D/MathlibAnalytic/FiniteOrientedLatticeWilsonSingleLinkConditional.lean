import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteLocality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Exact single-link Boltzmann weight obtained by varying one physical link. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-L.beta * L.wilsonAction (L.replaceLink A target g)))

/-- Every orientation-correct single-link Boltzmann weight is positive. -/
theorem finite_oriented_singleLinkBoltzmannWeight_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    0 < L.singleLinkBoltzmannWeight A target g := by
  rw [FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- Exact single-link conditional partition function. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ∑' g : L.Gauge, L.singleLinkBoltzmannWeight A target g

/-- The exact single-link conditional partition function is nonzero. -/
theorem finite_oriented_singleLinkPartitionFunction_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkPartitionFunction A target ≠ 0 := by
  intro hZero
  have hAll :
      ∀ g : L.Gauge, L.singleLinkBoltzmannWeight A target g = 0 := by
    simpa [FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction] using
      (ENNReal.tsum_eq_zero.mp hZero)
  exact
    (ne_of_gt
      (finite_oriented_singleLinkBoltzmannWeight_pos
        L A target default))
      (hAll default)

end

end MathlibAnalytic
end MGAP4D
