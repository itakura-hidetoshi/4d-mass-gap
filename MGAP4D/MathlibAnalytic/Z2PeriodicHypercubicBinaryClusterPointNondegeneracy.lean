import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbeddingReindex
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteProkhorovNondegeneracy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
noncomputable section

noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceWeakLimit
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) : PhysicalFourDimensionalYangMillsWeakLimit :=
  let E := D.toPhysicalEmbedding.toLatticeEmbedding
  let R := E.reindex f hf
  R.toWeakLimit mu (by
    simpa only [PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex_embeddedMeasure]
      using hmu)

theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceApproximatingVariance_eq
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) (n : ℕ) :
    (D.subsequenceWeakLimit f hf mu hmu).approximatingObservableVariance n
        D.toPhysicalEmbedding.observable = D.trajectory.gibbsVariance (f n) := by
  let E := D.toPhysicalEmbedding.toLatticeEmbedding
  unfold Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceWeakLimit
  rw [physical_yang_mills_latticeEmbedding_approximatingObservableVariance_eq_pullback]
  change E.latticePullbackObservableVariance (f n)
      D.toPhysicalEmbedding.observable = D.trajectory.gibbsVariance (f n)
  exact D.toPhysicalEmbedding.latticePullbackVariance_eq (f n)

noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceCertificate
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    (D.subsequenceWeakLimit f hf mu hmu).ObservableNontrivialityCertificate :=
  { observable := D.toPhysicalEmbedding.observable
    lowerBound := Real.exp (-(6 * D.betaUpper)) / 8
    lowerBound_pos :=
      z2PeriodicHypercubic_boundedCoupling_varianceLower_pos D.betaUpper
    approximating_variance_ge := by
      intro n
      rw [D.subsequenceApproximatingVariance_eq f hf mu hmu n]
      exact D.trajectory.uniform_gibbsVariance_lower_of_beta_le
        D.betaUpper D.beta_le (f n) }

theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceContinuumVariance_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    0 < (D.subsequenceWeakLimit f hf mu hmu).continuumObservableVariance
      D.toPhysicalEmbedding.observable :=
  (D.subsequenceCertificate f hf mu hmu).continuum_variance_pos

theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceContinuumMeasure_ne_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu))
    (b : D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration) :
    (mu : Measure D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration) ≠
      Measure.dirac b := by
  intro hDirac
  have hpos := D.subsequenceContinuumVariance_pos f hf mu hmu
  unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance at hpos
  change
    0 <
      (∫ A,
          (D.toPhysicalEmbedding.observable * D.toPhysicalEmbedding.observable) A
            ∂(mu : Measure
              D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)) -
        (∫ A, D.toPhysicalEmbedding.observable A
            ∂(mu : Measure
              D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)) ^ 2
    at hpos
  rw [hDirac] at hpos
  simp [pow_two] at hpos

end
end MathlibAnalytic
end MGAP4D
