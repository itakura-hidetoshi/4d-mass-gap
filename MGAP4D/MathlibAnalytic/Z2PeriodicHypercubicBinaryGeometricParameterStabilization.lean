import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryParameterCauchyCriterion
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A geometric inter-scale stabilization estimate for the finite-volume
Bernoulli coordinate. -/
structure GeometricBernoulliIncrementBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  /-- Multiplicative prefactor in the increment estimate. -/
  prefactor : ℝ
  /-- Geometric contraction ratio. -/
  ratio : ℝ
  prefactor_nonneg : 0 ≤ prefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  /-- Consecutive Bernoulli parameters contract at a geometric rate. -/
  abs_increment_le :
    ∀ n : ℕ,
      |D.embeddedBernoulliParameter (n + 1) -
          D.embeddedBernoulliParameter n| ≤
        prefactor * ratio ^ n

namespace GeometricBernoulliIncrementBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- The geometric majorant is summable. -/
theorem majorant_summable
    (G : GeometricBernoulliIncrementBound D) :
    Summable fun n : ℕ => G.prefactor * G.ratio ^ n := by
  exact (summable_geometric_of_lt_one G.ratio_nonneg G.ratio_lt_one).mul_left
    G.prefactor

/-- Geometric inter-scale decay makes the absolute parameter increments
summable. -/
theorem abs_increment_summable
    (G : GeometricBernoulliIncrementBound D) :
    Summable fun n : ℕ =>
      |D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n| := by
  refine Summable.of_nonneg_of_le
    (fun n : ℕ => abs_nonneg
      (D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n))
    G.abs_increment_le
    G.majorant_summable

/-- A geometric increment estimate therefore gives weak convergence of the full
embedded Boolean plaquette-law sequence. -/
theorem fullWeakConvergence
    (G : GeometricBernoulliIncrementBound D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  D.fullWeakConvergence_of_summable_abs_parameter_increment
    G.abs_increment_summable

/-- The finite-volume Bernoulli coordinate converges to the canonical continuum
parameter under the same geometric estimate. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (G : GeometricBernoulliIncrementBound D) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  D.embeddedMeasure_tendsto_prokhorov_iff_parameter_tendsto.mp
    G.fullWeakConvergence

/-- Every supplied strict-subsequence weak limit is the canonical Prokhorov
limit once geometric inter-scale stabilization holds. -/
theorem clusterPoint_eq_prokhorov
    (G : GeometricBernoulliIncrementBound D)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  have hCanonicalAlongSubsequence :
      Tendsto
        (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
        atTop (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
    G.fullWeakConvergence.comp hf.tendsto_atTop
  exact tendsto_nhds_unique hμ hCanonicalAlongSubsequence

/-- Geometric stabilization simultaneously supplies full weak convergence and
uniqueness of every strict-subsequence weak limit. -/
theorem fullWeakConvergence_and_clusterPointUniqueness
    (G : GeometricBernoulliIncrementBound D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
        (nhds D.prokhorovSubsequenceLimit.continuumMeasure) ∧
      ∀ (f : ℕ → ℕ), StrictMono f →
        ∀ μ : ProbabilityMeasure
          D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration,
          Tendsto
              (fun n =>
                D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
              atTop (nhds μ) →
            μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  refine ⟨G.fullWeakConvergence, ?_⟩
  intro f hf μ hμ
  exact G.clusterPoint_eq_prokhorov f hf μ hμ

end GeometricBernoulliIncrementBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
