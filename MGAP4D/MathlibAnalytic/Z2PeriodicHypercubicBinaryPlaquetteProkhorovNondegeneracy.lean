import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteProkhorov
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Along the canonical Prokhorov subsequence, the generic approximating
variance is exactly the finite periodic `Z₂` plaquette Gibbs variance at the
selected original lattice scale. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovApproximatingVariance_eq
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (n : ℕ) :
    D.prokhorovWeakLimit.approximatingObservableVariance n
        D.toPhysicalEmbedding.observable =
      D.trajectory.gibbsVariance
        (D.prokhorovSubsequenceLimit.subsequence n) := by
  let E := D.toPhysicalEmbedding.toLatticeEmbedding
  let k := D.prokhorovSubsequenceLimit.subsequence n
  change
    (∫ A, (D.toPhysicalEmbedding.observable * D.toPhysicalEmbedding.observable) A
          ∂(E.embeddedMeasure k : Measure E.PhysicalConfiguration)) -
        (∫ A, D.toPhysicalEmbedding.observable A
          ∂(E.embeddedMeasure k : Measure E.PhysicalConfiguration)) ^ 2 =
      D.trajectory.gibbsVariance k
  calc
    _ = E.latticePullbackObservableVariance k D.toPhysicalEmbedding.observable :=
      physical_yang_mills_latticeEmbedding_embeddedMeasure_variance_eq_pullback
        E k D.toPhysicalEmbedding.observable
    _ = D.trajectory.gibbsVariance k := by
      exact D.toPhysicalEmbedding.latticePullbackVariance_eq k

/-- The bounded-coupling finite-volume lower bound survives reindexing by the
canonical Prokhorov subsequence. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovObservableNontrivialityCertificate
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.prokhorovWeakLimit.ObservableNontrivialityCertificate :=
  { observable := D.toPhysicalEmbedding.observable
    lowerBound := Real.exp (-(6 * D.betaUpper)) / 8
    lowerBound_pos :=
      z2PeriodicHypercubic_boundedCoupling_varianceLower_pos D.betaUpper
    approximating_variance_ge := by
      intro n
      rw [D.prokhorovApproximatingVariance_eq n]
      exact D.trajectory.uniform_gibbsVariance_lower_of_beta_le
        D.betaUpper D.beta_le (D.prokhorovSubsequenceLimit.subsequence n) }

/-- The automatically extracted binary plaquette weak limit has strictly
positive variance for its canonical `0/1` observable. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuumVariance_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    0 < D.prokhorovWeakLimit.continuumObservableVariance
      D.toPhysicalEmbedding.observable :=
  D.prokhorovObservableNontrivialityCertificate.continuum_variance_pos

/-- The continuum probability law selected by compactness differs from every
Dirac probability law on its physical carrier. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuumMeasure_ne_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (b : D.prokhorovWeakLimit.Configuration) :
    (D.prokhorovWeakLimit.continuumMeasure :
        Measure D.prokhorovWeakLimit.Configuration) ≠
      Measure.dirac b := by
  intro hDirac
  have hVariancePos := D.prokhorovContinuumVariance_pos
  unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance at hVariancePos
  rw [hDirac] at hVariancePos
  simp [pow_two] at hVariancePos

/-- The automatically selected continuum binary plaquette law is not a
one-point probability law. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuumMeasure_not_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    ¬ ∃ b : D.prokhorovWeakLimit.Configuration,
      (D.prokhorovWeakLimit.continuumMeasure :
          Measure D.prokhorovWeakLimit.Configuration) =
        Measure.dirac b := by
  rintro ⟨b, hDirac⟩
  exact D.prokhorovContinuumMeasure_ne_dirac b hDirac

end

end MathlibAnalytic
end MGAP4D
