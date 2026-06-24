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

/-- The target-remote factor is nonzero. -/
theorem finite_oriented_targetRemoteBoltzmannFactor_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetRemoteBoltzmannFactor A target ≠ 0 :=
  ne_of_gt (finite_oriented_targetRemoteBoltzmannFactor_pos L A target)

/-- The target-remote factor is finite. -/
theorem finite_oriented_targetRemoteBoltzmannFactor_ne_top
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetRemoteBoltzmannFactor A target ≠ ∞ := by
  simp [FiniteOrientedLatticeWilsonSystem.targetRemoteBoltzmannFactor]

end

end MathlibAnalytic
end MGAP4D
