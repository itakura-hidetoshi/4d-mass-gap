import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteProkhorov
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEmbeddedObservableVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Along the canonical Prokhorov subsequence, the generic approximating
variance of the fixed binary observable is exactly the selected finite
plaquette Gibbs variance at the extracted lattice scale. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovApproximatingVariance_eq
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (n : ℕ) :
    D.prokhorovWeakLimit.approximatingObservableVariance n
        z2BinaryPlaquetteObservable =
      D.trajectory.gibbsVariance
        (D.prokhorovSubsequenceLimit.subsequence n) := by
  let E := D.toPhysicalEmbedding.toLatticeEmbedding
  let L := D.prokhorovSubsequenceLimit
  unfold Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovWeakLimit
    PhysicalFourDimensionalYangMillsWeakLimit.approximatingObservableVariance
  change
    (∫ A : Bool, (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) A
        ∂(E.embeddedMeasure (L.subsequence n) : Measure Bool)) -
        (∫ A : Bool, z2BinaryPlaquetteObservable A
          ∂(E.embeddedMeasure (L.subsequence n) : Measure Bool)) ^ 2 =
      D.trajectory.gibbsVariance (L.subsequence n)
  calc
    (∫ A : Bool, (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) A
        ∂(E.embeddedMeasure (L.subsequence n) : Measure Bool)) -
        (∫ A : Bool, z2BinaryPlaquetteObservable A
          ∂(E.embeddedMeasure (L.subsequence n) : Measure Bool)) ^ 2 =
      E.latticePullbackObservableVariance
        (L.subsequence n) z2BinaryPlaquetteObservable :=
      physical_yang_mills_latticeEmbedding_embeddedMeasure_variance_eq_pullback
        E (L.subsequence n) z2BinaryPlaquetteObservable
    _ = D.trajectory.gibbsVariance (L.subsequence n) :=
      D.toPhysicalEmbedding.latticePullbackVariance_eq (L.subsequence n)

/-- The bounded-coupling variance lower bound survives the automatically
selected Prokhorov subsequence. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovObservableNontrivialityCertificate
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.prokhorovWeakLimit.ObservableNontrivialityCertificate :=
  { observable := z2BinaryPlaquetteObservable
    lowerBound := Real.exp (-(6 * D.betaUpper)) / 8
    lowerBound_pos :=
      z2PeriodicHypercubic_boundedCoupling_varianceLower_pos D.betaUpper
    approximating_variance_ge := by
      intro n
      rw [D.prokhorovApproximatingVariance_eq n]
      exact D.trajectory.uniform_gibbsVariance_lower_of_beta_le
        D.betaUpper D.beta_le (D.prokhorovSubsequenceLimit.subsequence n) }

/-- The automatically extracted binary weak limit has strictly positive
variance for the canonical plaquette observable. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuum_variance_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    0 < D.prokhorovWeakLimit.continuumObservableVariance
      z2BinaryPlaquetteObservable :=
  D.prokhorovObservableNontrivialityCertificate.continuum_variance_pos

/-- The continuum law selected automatically by compactness and Prokhorov is
not a Dirac mass at either Boolean value. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuumMeasure_ne_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (b : Bool) :
    (D.prokhorovSubsequenceLimit.continuumMeasure : Measure Bool) ≠
      Measure.dirac b := by
  intro hDirac
  have hVariancePos := D.prokhorovContinuum_variance_pos
  unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance at hVariancePos
  change
    0 <
      (∫ A : Bool,
          (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) A
            ∂(D.prokhorovSubsequenceLimit.continuumMeasure : Measure Bool)) -
        (∫ A : Bool, z2BinaryPlaquetteObservable A
            ∂(D.prokhorovSubsequenceLimit.continuumMeasure : Measure Bool)) ^ 2
      at hVariancePos
  rw [hDirac] at hVariancePos
  fin_cases b <;>
    norm_num [z2BinaryPlaquetteObservable, pow_two] at hVariancePos

/-- Thus the automatically extracted binary continuum law is not any one-point
probability law. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuumMeasure_not_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    ¬ ∃ b : Bool,
      (D.prokhorovSubsequenceLimit.continuumMeasure : Measure Bool) =
        Measure.dirac b := by
  rintro ⟨b, hDirac⟩
  exact D.prokhorovContinuumMeasure_ne_dirac b hDirac

end

end MathlibAnalytic
end MGAP4D
