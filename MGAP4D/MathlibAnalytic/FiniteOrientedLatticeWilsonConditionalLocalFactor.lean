import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditional

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Target-local single-link Boltzmann factor. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-L.beta *
        L.targetLocalPlaquetteAction
          (L.replaceLink A target g) target))

/-- The target-local factor is positive. -/
theorem finite_oriented_targetLocalSingleLinkBoltzmannWeight_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    0 < L.targetLocalSingleLinkBoltzmannWeight A target g := by
  rw [FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- Target-remote factor common to all values inserted at the target link. -/
def FiniteOrientedLatticeWilsonSystem.targetRemoteBoltzmannFactor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-L.beta * L.targetRemotePlaquetteAction A target))

/-- The target-remote factor is positive. -/
theorem finite_oriented_targetRemoteBoltzmannFactor_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    0 < L.targetRemoteBoltzmannFactor A target := by
  rw [FiniteOrientedLatticeWilsonSystem.targetRemoteBoltzmannFactor,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

end

end MathlibAnalytic
end MGAP4D
