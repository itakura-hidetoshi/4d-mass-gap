import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryGeometricParameterStabilization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A uniform inter-scale Lipschitz estimate transferring changes of the lattice
coupling to changes of the embedded Bernoulli coordinate. -/
structure BernoulliBetaIncrementLipschitzBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  abs_parameter_increment_le :
    ∀ n : ℕ,
      |D.embeddedBernoulliParameter (n + 1) -
          D.embeddedBernoulliParameter n| ≤
        factor *
          |D.trajectory.beta (n + 1) - D.trajectory.beta n|

/-- A geometric stabilization estimate for consecutive lattice-coupling
increments. -/
structure GeometricBetaIncrementBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  prefactor : ℝ
  ratio : ℝ
  prefactor_nonneg : 0 ≤ prefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  abs_beta_increment_le :
    ∀ n : ℕ,
      |D.trajectory.beta (n + 1) - D.trajectory.beta n| ≤
        prefactor * ratio ^ n

namespace BernoulliBetaIncrementLipschitzBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- A Lipschitz transfer estimate and geometric coupling stabilization combine
into geometric stabilization of the Bernoulli coordinate. -/
noncomputable def toGeometricBernoulliIncrementBound
    (L : BernoulliBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D) :
    GeometricBernoulliIncrementBound D :=
  { prefactor := L.factor * B.prefactor
    ratio := B.ratio
    prefactor_nonneg := mul_nonneg L.factor_nonneg B.prefactor_nonneg
    ratio_nonneg := B.ratio_nonneg
    ratio_lt_one := B.ratio_lt_one
    abs_increment_le := by
      intro n
      calc
        |D.embeddedBernoulliParameter (n + 1) -
            D.embeddedBernoulliParameter n| ≤
            L.factor *
              |D.trajectory.beta (n + 1) - D.trajectory.beta n| :=
          L.abs_parameter_increment_le n
        _ ≤ L.factor * (B.prefactor * B.ratio ^ n) :=
          mul_le_mul_of_nonneg_left (B.abs_beta_increment_le n)
            L.factor_nonneg
        _ = (L.factor * B.prefactor) * B.ratio ^ n := by ring }

/-- The combined inter-scale estimates imply absolute summability of the
finite-volume Bernoulli increments. -/
theorem abs_parameter_increment_summable
    (L : BernoulliBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D) :
    Summable fun n : ℕ =>
      |D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n| :=
  (L.toGeometricBernoulliIncrementBound B).abs_increment_summable

/-- The combined estimates imply weak convergence of the full embedded
plaquette-law sequence. -/
theorem fullWeakConvergence
    (L : BernoulliBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  (L.toGeometricBernoulliIncrementBound B).fullWeakConvergence

/-- The finite-volume Bernoulli coordinate converges to the canonical continuum
parameter under the combined coupling estimates. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (L : BernoulliBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  (L.toGeometricBernoulliIncrementBound B)
    .embeddedBernoulliParameter_tendsto_prokhorov

/-- Every supplied strict-subsequence weak limit is canonical under the
Lipschitz-transfer and geometric-coupling hypotheses. -/
theorem clusterPoint_eq_prokhorov
    (L : BernoulliBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure :=
  (L.toGeometricBernoulliIncrementBound B).clusterPoint_eq_prokhorov
    f hf μ hμ

end BernoulliBetaIncrementLipschitzBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
