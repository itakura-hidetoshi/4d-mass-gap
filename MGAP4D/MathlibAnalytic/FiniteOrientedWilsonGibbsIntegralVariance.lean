import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEmbeddedObservableVariance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The finite oriented Wilson Gibbs law bundled as a Mathlib probability
measure. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.gibbsProbabilityMeasure
    (L : FiniteOrientedLatticeWilsonSystem) :
    ProbabilityMeasure L.Configuration :=
  ⟨L.gibbsMeasure,
    finiteOrientedLatticeWilsonSystem_gibbsMeasure_isProbabilityMeasure L⟩

@[simp]
theorem finite_oriented_gibbsProbabilityMeasure_toMeasure
    (L : FiniteOrientedLatticeWilsonSystem) :
    (L.gibbsProbabilityMeasure : Measure L.Configuration) = L.gibbsMeasure :=
  rfl

/-- The existing finite-sum Gibbs expectation is exactly the Bochner integral
against the finite oriented Wilson Gibbs measure. -/
theorem finite_oriented_gibbsExpectationReal_eq_integral
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal f = ∫ A, f A ∂L.gibbsMeasure := by
  classical
  rw [FiniteOrientedLatticeWilsonSystem.gibbsMeasure, PMF.integral_eq_sum]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  simp only [smul_eq_mul]

/-- Every real observable on the finite oriented configuration space is
measurable. -/
theorem finite_oriented_observable_measurable
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    Measurable f :=
  measurable_of_finite f

/-- The existing finite-sum Gibbs variance is Mathlib's measure-theoretic
variance under the finite oriented Wilson Gibbs measure. -/
theorem finite_oriented_gibbsVarianceReal_eq_variance
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsVarianceReal f = ProbabilityTheory.variance f L.gibbsMeasure := by
  classical
  rw [ProbabilityTheory.variance_eq_integral
    (finite_oriented_observable_measurable L f).aemeasurable]
  rw [← finite_oriented_gibbsExpectationReal_eq_integral L f]
  rw [FiniteOrientedLatticeWilsonSystem.gibbsMeasure, PMF.integral_eq_sum]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  simp only [smul_eq_mul]

/-- Every real observable on a finite oriented configuration space belongs to
`L²` for its Gibbs probability measure. -/
theorem finite_oriented_observable_memLp_two
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    MemLp f 2 L.gibbsMeasure := by
  let sf : SimpleFunc L.Configuration ℝ := SimpleFunc.ofFinite f
  have hsf : MemLp (sf : L.Configuration → ℝ) 2 L.gibbsMeasure :=
    sf.memLp_of_isFiniteMeasure 2 L.gibbsMeasure
  simpa [sf] using hsf

/-- The finite oriented Gibbs variance also has the usual second-moment minus
squared-mean form. -/
theorem finite_oriented_gibbsVarianceReal_eq_secondMoment_sub_mean_sq
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsVarianceReal f =
      (∫ A, f A ^ 2 ∂L.gibbsMeasure) -
        (∫ A, f A ∂L.gibbsMeasure) ^ 2 := by
  rw [finite_oriented_gibbsVarianceReal_eq_variance]
  exact ProbabilityTheory.variance_eq_sub
    (finite_oriented_observable_memLp_two L f)

/-- Pointwise equality of a physical observable pullback with a lattice
observable identifies their lattice pullback variances. -/
theorem physical_yang_mills_latticePullbackObservableVariance_eq_of_pointwise
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (n : ℕ)
    (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (f : E.LatticeConfiguration n → ℝ)
    (hPullback : ∀ a, O (E.interpolate n a) = f a) :
    E.latticePullbackObservableVariance n O =
      (∫ a, f a ^ 2
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n))) -
        (∫ a, f a
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n))) ^ 2 := by
  unfold PhysicalFourDimensionalYangMillsLatticeEmbedding.latticePullbackObservableVariance
  have hFirst :
      (∫ a, O (E.interpolate n a)
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n))) =
        ∫ a, f a
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) := by
    apply integral_congr_ae
    filter_upwards [] with a
    exact hPullback a
  have hSecond :
      (∫ a, (O * O) (E.interpolate n a)
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n))) =
        ∫ a, f a ^ 2
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) := by
    apply integral_congr_ae
    filter_upwards [] with a
    simp [hPullback a, pow_two]
  rw [hFirst, hSecond]

end

end MathlibAnalytic
end MGAP4D
