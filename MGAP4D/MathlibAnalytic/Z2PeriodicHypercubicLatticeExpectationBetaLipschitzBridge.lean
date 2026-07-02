import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryParameterLatticeExpectation
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryBetaLipschitzGeometricBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- The original finite-volume Gibbs expectation of the selected plaquette
observable. -/
noncomputable def latticePlaquetteExpectation
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) : ℝ :=
  ∫ A : (D.trajectory.system k).Configuration,
    D.trajectory.plaquetteObservable k A
      ∂((D.trajectory.system k).gibbsProbabilityMeasure :
        Measure (D.trajectory.system k).Configuration)

/-- The scalar Bernoulli coordinate is exactly the finite-volume lattice
plaquette expectation. -/
theorem embeddedBernoulliParameter_eq_latticePlaquetteExpectation'
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    D.embeddedBernoulliParameter k = D.latticePlaquetteExpectation k := by
  exact D.embeddedBernoulliParameter_eq_latticePlaquetteExpectation k

/-- A direct Lipschitz estimate for consecutive finite-volume Gibbs plaquette
expectations with respect to consecutive coupling increments. -/
structure LatticePlaquetteExpectationBetaIncrementLipschitzBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  abs_expectation_increment_le :
    ∀ n : ℕ,
      |D.latticePlaquetteExpectation (n + 1) -
          D.latticePlaquetteExpectation n| ≤
        factor * |D.trajectory.beta (n + 1) - D.trajectory.beta n|

namespace LatticePlaquetteExpectationBetaIncrementLipschitzBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- The lattice-expectation estimate transports exactly to the Bernoulli
coordinate used by the weak-convergence layer. -/
noncomputable def toBernoulliBetaIncrementLipschitzBound
    (L : LatticePlaquetteExpectationBetaIncrementLipschitzBound D) :
    BernoulliBetaIncrementLipschitzBound D :=
  { factor := L.factor
    factor_nonneg := L.factor_nonneg
    abs_parameter_increment_le := by
      intro n
      rw [D.embeddedBernoulliParameter_eq_latticePlaquetteExpectation',
        D.embeddedBernoulliParameter_eq_latticePlaquetteExpectation']
      exact L.abs_expectation_increment_le n }

/-- Combined with geometric coupling stabilization, the lattice expectation
estimate gives full weak convergence of the embedded plaquette laws. -/
theorem fullWeakConvergence
    (L : LatticePlaquetteExpectationBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  (L.toBernoulliBetaIncrementLipschitzBound).fullWeakConvergence B

/-- The finite-volume Bernoulli coordinate converges to the canonical continuum
parameter under the same two lattice-level estimates. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (L : LatticePlaquetteExpectationBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  (L.toBernoulliBetaIncrementLipschitzBound)
    .embeddedBernoulliParameter_tendsto_prokhorov B

/-- Every strict-subsequence weak limit is canonical under the lattice-level
Lipschitz estimate and geometric coupling stabilization. -/
theorem clusterPoint_eq_prokhorov
    (L : LatticePlaquetteExpectationBetaIncrementLipschitzBound D)
    (B : GeometricBetaIncrementBound D)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure :=
  (L.toBernoulliBetaIncrementLipschitzBound).clusterPoint_eq_prokhorov
    B f hf μ hμ

end LatticePlaquetteExpectationBetaIncrementLipschitzBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
