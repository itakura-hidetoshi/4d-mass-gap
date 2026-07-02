import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryBetaLipschitzGeometricBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Decompose one inter-scale change of the Bernoulli coordinate into a genuine
finite-volume or geometry error and a coupling-sensitivity contribution.

Unlike a coupling-only estimate, this interface does not force equality of
plaquette marginals when the coupling is fixed but the lattice geometry changes. -/
structure BernoulliGeometryBetaIncrementDecomposition
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  couplingFactor : ℝ
  couplingFactor_nonneg : 0 ≤ couplingFactor
  geometryError : ℕ → ℝ
  geometryError_nonneg : ∀ n, 0 ≤ geometryError n
  abs_parameter_increment_le :
    ∀ n : ℕ,
      |D.embeddedBernoulliParameter (n + 1) -
          D.embeddedBernoulliParameter n| ≤
        geometryError n + couplingFactor *
          |D.trajectory.beta (n + 1) - D.trajectory.beta n|

/-- A common geometric rate controls both the finite-volume geometry error and
the lattice-coupling increments. -/
structure GeometricGeometryBetaControl
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (A : BernoulliGeometryBetaIncrementDecomposition D) where
  geometryPrefactor : ℝ
  betaPrefactor : ℝ
  ratio : ℝ
  geometryPrefactor_nonneg : 0 ≤ geometryPrefactor
  betaPrefactor_nonneg : 0 ≤ betaPrefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  geometryError_le :
    ∀ n : ℕ, A.geometryError n ≤ geometryPrefactor * ratio ^ n
  abs_beta_increment_le :
    ∀ n : ℕ,
      |D.trajectory.beta (n + 1) - D.trajectory.beta n| ≤
        betaPrefactor * ratio ^ n

namespace BernoulliGeometryBetaIncrementDecomposition

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Geometric control of both inter-scale contributions produces the geometric
Bernoulli increment estimate required by the convergence theorem. -/
noncomputable def toGeometricBernoulliIncrementBound
    (A : BernoulliGeometryBetaIncrementDecomposition D)
    (G : GeometricGeometryBetaControl D A) :
    GeometricBernoulliIncrementBound D :=
  { prefactor := G.geometryPrefactor + A.couplingFactor * G.betaPrefactor
    ratio := G.ratio
    prefactor_nonneg :=
      add_nonneg G.geometryPrefactor_nonneg
        (mul_nonneg A.couplingFactor_nonneg G.betaPrefactor_nonneg)
    ratio_nonneg := G.ratio_nonneg
    ratio_lt_one := G.ratio_lt_one
    abs_increment_le := by
      intro n
      calc
        |D.embeddedBernoulliParameter (n + 1) -
            D.embeddedBernoulliParameter n| ≤
            A.geometryError n + A.couplingFactor *
              |D.trajectory.beta (n + 1) - D.trajectory.beta n| :=
          A.abs_parameter_increment_le n
        _ ≤ G.geometryPrefactor * G.ratio ^ n +
            A.couplingFactor * (G.betaPrefactor * G.ratio ^ n) := by
          exact add_le_add (G.geometryError_le n)
            (mul_le_mul_of_nonneg_left (G.abs_beta_increment_le n)
              A.couplingFactor_nonneg)
        _ = (G.geometryPrefactor +
              A.couplingFactor * G.betaPrefactor) * G.ratio ^ n := by
          ring }

/-- The decomposed geometry-plus-coupling estimate makes the absolute Bernoulli
increments summable. -/
theorem abs_parameter_increment_summable
    (A : BernoulliGeometryBetaIncrementDecomposition D)
    (G : GeometricGeometryBetaControl D A) :
    Summable fun n : ℕ =>
      |D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n| :=
  (A.toGeometricBernoulliIncrementBound G).abs_increment_summable

/-- Geometric decay of both the lattice-geometry error and the coupling
increments gives weak convergence of the complete embedded measure sequence. -/
theorem fullWeakConvergence
    (A : BernoulliGeometryBetaIncrementDecomposition D)
    (G : GeometricGeometryBetaControl D A) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  (A.toGeometricBernoulliIncrementBound G).fullWeakConvergence

/-- The scalar plaquette parameter converges to the canonical continuum
parameter under the decomposed estimate. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (A : BernoulliGeometryBetaIncrementDecomposition D)
    (G : GeometricGeometryBetaControl D A) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  GeometricBernoulliIncrementBound.embeddedBernoulliParameter_tendsto_prokhorov
    (A.toGeometricBernoulliIncrementBound G)

/-- Every convergent strict subsequence has the same canonical continuum law. -/
theorem clusterPoint_eq_prokhorov
    (A : BernoulliGeometryBetaIncrementDecomposition D)
    (G : GeometricGeometryBetaControl D A)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure :=
  (A.toGeometricBernoulliIncrementBound G).clusterPoint_eq_prokhorov
    f hf μ hμ

end BernoulliGeometryBetaIncrementDecomposition

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
