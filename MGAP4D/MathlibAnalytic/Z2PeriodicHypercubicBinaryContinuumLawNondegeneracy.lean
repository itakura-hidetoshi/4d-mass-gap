import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteEmbedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Positive variance of the canonical binary plaquette observable prevents the
continuum binary law from collapsing to a Dirac mass at either Boolean value. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.continuumMeasure_ne_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (continuumMeasure : ProbabilityMeasure Bool)
    (hWeak : Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
      atTop (nhds continuumMeasure))
    (b : Bool) :
    (continuumMeasure : Measure Bool) ≠ Measure.dirac b := by
  intro hDirac
  have hVariancePos := D.continuum_variance_pos continuumMeasure hWeak
  unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance at hVariancePos
  change
    0 <
      (∫ A : Bool,
          (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) A
            ∂(continuumMeasure : Measure Bool)) -
        (∫ A : Bool, z2BinaryPlaquetteObservable A
            ∂(continuumMeasure : Measure Bool)) ^ 2 at hVariancePos
  rw [hDirac] at hVariancePos
  simpa [pow_two] using hVariancePos

/-- The continuum binary plaquette law is not any one-point probability law. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.continuumMeasure_not_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (continuumMeasure : ProbabilityMeasure Bool)
    (hWeak : Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
      atTop (nhds continuumMeasure)) :
    ¬ ∃ b : Bool, (continuumMeasure : Measure Bool) = Measure.dirac b := by
  rintro ⟨b, hDirac⟩
  exact D.continuumMeasure_ne_dirac continuumMeasure hWeak b hDirac

end

end MathlibAnalytic
end MGAP4D
