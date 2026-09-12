import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditional

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

/-- Global Boltzmann weight of an orientation-correct physical-link
configuration. -/
def FiniteOrientedLatticeWilsonSystem.boltzmannWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-L.beta * L.wilsonAction A))

/-- Every oriented finite-volume Boltzmann weight is strictly positive. -/
theorem finite_oriented_boltzmannWeight_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    0 < L.boltzmannWeight A := by
  rw [FiniteOrientedLatticeWilsonSystem.boltzmannWeight,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- Every oriented finite-volume Boltzmann weight is nonzero. -/
theorem finite_oriented_boltzmannWeight_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    L.boltzmannWeight A ≠ 0 :=
  ne_of_gt (finite_oriented_boltzmannWeight_pos L A)

/-- Global oriented Boltzmann weights are gauge invariant. -/
theorem finite_oriented_boltzmannWeight_gaugeInvariant
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.boltzmannWeight (L.gaugeTransform gamma A) =
      L.boltzmannWeight A := by
  simp only [FiniteOrientedLatticeWilsonSystem.boltzmannWeight]
  rw [finite_oriented_wilsonAction_gaugeInvariant]

/-- Global finite partition function on physical positive links. -/
def FiniteOrientedLatticeWilsonSystem.partitionFunction
    (L : FiniteOrientedLatticeWilsonSystem) : ℝ≥0∞ :=
  ∑' A : L.Configuration, L.boltzmannWeight A

/-- The oriented finite partition function is nonzero. -/
theorem finite_oriented_partitionFunction_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.partitionFunction ≠ 0 := by
  intro hZero
  have hAll : ∀ A : L.Configuration, L.boltzmannWeight A = 0 :=
    ENNReal.tsum_eq_zero.mp hZero
  exact finite_oriented_boltzmannWeight_ne_zero L default (hAll default)

/-- The oriented finite partition function is finite. -/
theorem finite_oriented_partitionFunction_ne_top
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.partitionFunction ≠ ∞ := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.partitionFunction
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun A _hA => by
    simp [FiniteOrientedLatticeWilsonSystem.boltzmannWeight]

/-- Normalized orientation-correct finite Wilson Gibbs law. -/
def FiniteOrientedLatticeWilsonSystem.gibbsPMF
    (L : FiniteOrientedLatticeWilsonSystem) : PMF L.Configuration :=
  PMF.normalize L.boltzmannWeight
    (finite_oriented_partitionFunction_ne_zero L)
    (finite_oriented_partitionFunction_ne_top L)

/-- Pointwise formula for the oriented Gibbs law. -/
theorem finite_oriented_gibbsPMF_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    L.gibbsPMF A =
      L.boltzmannWeight A * L.partitionFunction⁻¹ := by
  rfl

/-- The oriented Gibbs PMF is gauge invariant. -/
theorem finite_oriented_gibbsPMF_gaugeInvariant
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.gibbsPMF (L.gaugeTransform gamma A) = L.gibbsPMF A := by
  rw [finite_oriented_gibbsPMF_apply,
    finite_oriented_gibbsPMF_apply,
    finite_oriented_boltzmannWeight_gaugeInvariant]

/-- Concrete finite-volume Euclidean measure of the oriented Wilson system. -/
def FiniteOrientedLatticeWilsonSystem.gibbsMeasure
    (L : FiniteOrientedLatticeWilsonSystem) : Measure L.Configuration :=
  L.gibbsPMF.toMeasure

/-- The oriented Gibbs measure is a probability measure. -/
instance finiteOrientedLatticeWilsonSystem_gibbsMeasure_isProbabilityMeasure
    (L : FiniteOrientedLatticeWilsonSystem) :
    IsProbabilityMeasure L.gibbsMeasure := by
  unfold FiniteOrientedLatticeWilsonSystem.gibbsMeasure
  infer_instance

/-- Singleton masses equal normalized oriented Boltzmann weights. -/
theorem finite_oriented_gibbsMeasure_singleton
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    L.gibbsMeasure ({A} : Set L.Configuration) =
      L.boltzmannWeight A * L.partitionFunction⁻¹ := by
  rw [FiniteOrientedLatticeWilsonSystem.gibbsMeasure,
    L.gibbsPMF.toMeasure_apply_singleton A (measurableSet_singleton A)]
  exact finite_oriented_gibbsPMF_apply L A

/-- Gauge invariance of all oriented singleton masses. -/
theorem finite_oriented_gibbsMeasure_singleton_gaugeInvariant
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.gibbsMeasure
        ({L.gaugeTransform gamma A} : Set L.Configuration) =
      L.gibbsMeasure ({A} : Set L.Configuration) := by
  rw [finite_oriented_gibbsMeasure_singleton,
    finite_oriented_gibbsMeasure_singleton,
    finite_oriented_boltzmannWeight_gaugeInvariant]

end

end MathlibAnalytic
end MGAP4D
