import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryParameterCauchyCriterion
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Quantitative inter-scale control for the finite-volume Bernoulli parameter.
The consecutive increments decay at a geometric rate. -/
structure
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.GeometricScaleControl
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  prefactor : ℝ
  ratio : ℝ
  prefactor_nonneg : 0 ≤ prefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  increment_le : ∀ n : ℕ,
    |D.embeddedBernoulliParameter (n + 1) -
      D.embeddedBernoulliParameter n| ≤ prefactor * ratio ^ n

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.GeometricScaleControl

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- The geometric majorant itself is summable. -/
theorem summable_majorant
    (G : D.GeometricScaleControl) :
    Summable (fun n : ℕ => G.prefactor * G.ratio ^ n) := by
  have hNorm : ‖G.ratio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg G.ratio_nonneg]
    exact G.ratio_lt_one
  exact (summable_geometric_of_norm_lt_one hNorm).mul_left G.prefactor

/-- Geometric inter-scale control makes the absolute consecutive parameter
increments summable. -/
theorem summable_abs_parameter_increment
    (G : D.GeometricScaleControl) :
    Summable fun n : ℕ =>
      |D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n| := by
  apply G.summable_majorant.of_nonneg_of_le
  · intro n
    exact abs_nonneg _
  · exact G.increment_le

/-- Therefore geometric inter-scale control forces weak convergence of the full
embedded binary plaquette-law sequence. -/
theorem fullWeakConvergence
    (G : D.GeometricScaleControl) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  D.fullWeakConvergence_of_summable_abs_parameter_increment
    G.summable_abs_parameter_increment

/-- Under geometric scale control, every subsequential weak limit is the
canonical Prokhorov limit. -/
theorem clusterPoint_eq_prokhorov
    (G : D.GeometricScaleControl)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  have hCauchy : CauchySeq D.embeddedBernoulliParameter :=
    (D.embeddedMeasure_tendsto_prokhorov_iff_parameter_cauchy.mp
      G.fullWeakConvergence)
  exact
    D.clusterPoint_eq_prokhorov_of_embeddedBernoulliParameter_cauchy
      hCauchy f hf μ hμ

/-- Consequently every cluster-point Bernoulli parameter equals the canonical
continuum parameter. -/
theorem clusterPointBernoulliParameter_eq_prokhorov
    (G : D.GeometricScaleControl)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    D.clusterPointBernoulliParameter μ = D.prokhorovBernoulliParameter := by
  rw [G.clusterPoint_eq_prokhorov f hf μ hμ]
  rfl

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.GeometricScaleControl

end

end MathlibAnalytic
end MGAP4D
