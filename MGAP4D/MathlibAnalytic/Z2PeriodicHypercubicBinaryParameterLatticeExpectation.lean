import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryWeakConvergenceCriterion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- Change of variables for real bounded continuous observables under a lattice
embedding pushforward. -/
theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.integral_embeddedMeasure
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (f : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (n : ℕ) :
    (∫ x, f x ∂(E.embeddedMeasure n : Measure E.PhysicalConfiguration)) =
      ∫ u, f (E.interpolate n u)
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) := by
  change
    (∫ x, f x ∂Measure.map (E.interpolate n)
      (E.latticeMeasure n : Measure (E.LatticeConfiguration n))) = _
  exact MeasureTheory.integral_map
    (E.interpolate_measurable n).aemeasurable
    f.continuous.aestronglyMeasurable

/-- The finite-volume Bernoulli coordinate is the expectation of the canonical
binary observable under the embedded Boolean law. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter_eq_embeddedExpectation
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    D.embeddedBernoulliParameter k =
      ∫ b : Bool, z2BinaryPlaquetteObservable b
        ∂(D.boolEmbeddedMeasure k : Measure Bool) := by
  exact
    (probabilityMeasure_integral_z2BinaryPlaquetteObservable
      (D.boolEmbeddedMeasure k)).symm

/-- Pulling the embedded expectation back through the interpolation map recovers
the original finite-volume Gibbs expectation of the plaquette observable. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter_eq_latticePlaquetteExpectation
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    D.embeddedBernoulliParameter k =
      ∫ A : (D.trajectory.system k).Configuration,
        D.trajectory.plaquetteObservable k A
        ∂((D.trajectory.system k).gibbsProbabilityMeasure :
          Measure (D.trajectory.system k).Configuration) := by
  calc
    D.embeddedBernoulliParameter k =
        ∫ b : Bool, z2BinaryPlaquetteObservable b
          ∂(D.boolEmbeddedMeasure k : Measure Bool) :=
      D.embeddedBernoulliParameter_eq_embeddedExpectation k
    _ = ∫ A : (D.trajectory.system k).Configuration,
          z2BinaryPlaquetteObservable (D.trajectory.plaquetteBit k A)
          ∂((D.trajectory.system k).gibbsProbabilityMeasure :
            Measure (D.trajectory.system k).Configuration) := by
      change
        (∫ b : Bool, z2BinaryPlaquetteObservable b
          ∂(D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure k :
            Measure Bool)) = _
      exact
        D.toPhysicalEmbedding.toLatticeEmbedding.integral_embeddedMeasure
          z2BinaryPlaquetteObservable k
    _ = ∫ A : (D.trajectory.system k).Configuration,
          D.trajectory.plaquetteObservable k A
          ∂((D.trajectory.system k).gibbsProbabilityMeasure :
            Measure (D.trajectory.system k).Configuration) := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact D.trajectory.binaryObservable_pullback k A

/-- Consequently, the increment of the Bernoulli coordinate is exactly the
increment of the corresponding finite-volume Gibbs plaquette expectation. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter_increment_eq_latticeExpectation_increment
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    D.embeddedBernoulliParameter (k + 1) -
        D.embeddedBernoulliParameter k =
      (∫ A : (D.trajectory.system (k + 1)).Configuration,
          D.trajectory.plaquetteObservable (k + 1) A
          ∂((D.trajectory.system (k + 1)).gibbsProbabilityMeasure :
            Measure (D.trajectory.system (k + 1)).Configuration)) -
      ∫ A : (D.trajectory.system k).Configuration,
          D.trajectory.plaquetteObservable k A
          ∂((D.trajectory.system k).gibbsProbabilityMeasure :
            Measure (D.trajectory.system k).Configuration) := by
  rw [D.embeddedBernoulliParameter_eq_latticePlaquetteExpectation,
    D.embeddedBernoulliParameter_eq_latticePlaquetteExpectation]

end

end MathlibAnalytic
end MGAP4D
