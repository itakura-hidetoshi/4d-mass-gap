import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryExactGeometryBetaSplitting
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryGeometricParameterStabilization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Separate geometric-rate estimates for the exact coupling-response and
geometry-response terms of the finite-volume plaquette expectation increment. -/
structure GeometricPlaquetteResponseControl
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  couplingPrefactor : ℝ
  geometryPrefactor : ℝ
  ratio : ℝ
  couplingPrefactor_nonneg : 0 ≤ couplingPrefactor
  geometryPrefactor_nonneg : 0 ≤ geometryPrefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  abs_couplingResponse_le :
    ∀ k : ℕ,
      |D.couplingResponseIncrement k| ≤ couplingPrefactor * ratio ^ k
  abs_geometryResponse_le :
    ∀ k : ℕ,
      |D.geometryResponseIncrement k| ≤ geometryPrefactor * ratio ^ k

namespace GeometricPlaquetteResponseControl

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Separate geometric bounds for the two exact responses combine into the
geometric Bernoulli increment bound used by the convergence layer. -/
noncomputable def toGeometricBernoulliIncrementBound
    (R : GeometricPlaquetteResponseControl D) :
    GeometricBernoulliIncrementBound D :=
  { prefactor := R.couplingPrefactor + R.geometryPrefactor
    ratio := R.ratio
    prefactor_nonneg :=
      add_nonneg R.couplingPrefactor_nonneg R.geometryPrefactor_nonneg
    ratio_nonneg := R.ratio_nonneg
    ratio_lt_one := R.ratio_lt_one
    abs_increment_le := by
      intro k
      calc
        |D.embeddedBernoulliParameter (k + 1) -
            D.embeddedBernoulliParameter k| ≤
            |D.couplingResponseIncrement k| +
              |D.geometryResponseIncrement k| :=
          D.abs_embeddedBernoulliParameter_increment_le_responses k
        _ ≤ R.couplingPrefactor * R.ratio ^ k +
            R.geometryPrefactor * R.ratio ^ k :=
          add_le_add (R.abs_couplingResponse_le k)
            (R.abs_geometryResponse_le k)
        _ = (R.couplingPrefactor + R.geometryPrefactor) *
            R.ratio ^ k := by ring }

/-- The exact response estimates make the finite-volume Bernoulli increments
absolutely summable. -/
theorem abs_parameter_increment_summable
    (R : GeometricPlaquetteResponseControl D) :
    Summable fun k : ℕ =>
      |D.embeddedBernoulliParameter (k + 1) -
        D.embeddedBernoulliParameter k| :=
  R.toGeometricBernoulliIncrementBound.abs_increment_summable

/-- Geometric decay of the exact coupling and geometry responses gives weak
convergence of the complete embedded plaquette-law sequence. -/
theorem fullWeakConvergence
    (R : GeometricPlaquetteResponseControl D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  R.toGeometricBernoulliIncrementBound.fullWeakConvergence

/-- The finite-volume plaquette expectation converges to the canonical continuum
Bernoulli parameter. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (R : GeometricPlaquetteResponseControl D) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  GeometricBernoulliIncrementBound.embeddedBernoulliParameter_tendsto_prokhorov
    R.toGeometricBernoulliIncrementBound

/-- Every convergent strict subsequence has the same canonical continuum law. -/
theorem clusterPoint_eq_prokhorov
    (R : GeometricPlaquetteResponseControl D)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure :=
  R.toGeometricBernoulliIncrementBound.clusterPoint_eq_prokhorov
    f hf μ hμ

/-- The response-control certificate simultaneously gives full convergence and
uniqueness of all strict-subsequence weak limits. -/
theorem fullWeakConvergence_and_clusterPointUniqueness
    (R : GeometricPlaquetteResponseControl D) :
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
  refine ⟨R.fullWeakConvergence, ?_⟩
  intro f hf μ hμ
  exact R.clusterPoint_eq_prokhorov f hf μ hμ

end GeometricPlaquetteResponseControl

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
