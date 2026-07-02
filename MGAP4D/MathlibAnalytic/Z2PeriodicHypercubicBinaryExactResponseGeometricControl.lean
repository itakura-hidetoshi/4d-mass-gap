import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryExactGeometryBetaSplitting
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryGeometryBetaDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A fixed-lattice coupling-response estimate for the exact inter-scale
splitting. -/
structure ExactCouplingResponseLipschitzBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  abs_couplingResponse_le :
    ∀ n : ℕ,
      |D.couplingResponseIncrement n| ≤
        factor * |D.trajectory.beta (n + 1) - D.trajectory.beta n|

namespace ExactCouplingResponseLipschitzBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- The exact response splitting and a coupling-response Lipschitz estimate
produce the abstract geometry-plus-coupling decomposition. -/
noncomputable def toBernoulliGeometryBetaIncrementDecomposition
    (L : ExactCouplingResponseLipschitzBound D) :
    BernoulliGeometryBetaIncrementDecomposition D :=
  { couplingFactor := L.factor
    couplingFactor_nonneg := L.factor_nonneg
    geometryError := fun n => |D.geometryResponseIncrement n|
    geometryError_nonneg := fun n => abs_nonneg _
    abs_parameter_increment_le := by
      intro n
      have hSplit :=
        D.abs_embeddedBernoulliParameter_increment_le_responses n
      have hCoupling := L.abs_couplingResponse_le n
      linarith }

end ExactCouplingResponseLipschitzBound

/-- One common geometric rate controls the exact geometry response and the
coupling trajectory increments. -/
structure GeometricExactResponseControl
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (L : ExactCouplingResponseLipschitzBound D) where
  geometryPrefactor : ℝ
  betaPrefactor : ℝ
  ratio : ℝ
  geometryPrefactor_nonneg : 0 ≤ geometryPrefactor
  betaPrefactor_nonneg : 0 ≤ betaPrefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  abs_geometryResponse_le :
    ∀ n : ℕ,
      |D.geometryResponseIncrement n| ≤ geometryPrefactor * ratio ^ n
  abs_beta_increment_le :
    ∀ n : ℕ,
      |D.trajectory.beta (n + 1) - D.trajectory.beta n| ≤
        betaPrefactor * ratio ^ n

namespace GeometricExactResponseControl

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}
variable {L : ExactCouplingResponseLipschitzBound D}

/-- Exact geometric response bounds instantiate the abstract geometric control
used by the convergence theorem. -/
noncomputable def toGeometricGeometryBetaControl
    (G : GeometricExactResponseControl D L) :
    GeometricGeometryBetaControl D
      L.toBernoulliGeometryBetaIncrementDecomposition :=
  { geometryPrefactor := G.geometryPrefactor
    betaPrefactor := G.betaPrefactor
    ratio := G.ratio
    geometryPrefactor_nonneg := G.geometryPrefactor_nonneg
    betaPrefactor_nonneg := G.betaPrefactor_nonneg
    ratio_nonneg := G.ratio_nonneg
    ratio_lt_one := G.ratio_lt_one
    geometryError_le := G.abs_geometryResponse_le
    abs_beta_increment_le := G.abs_beta_increment_le }

/-- Geometric decay of both exact response terms makes the Bernoulli increments
absolutely summable. -/
theorem abs_parameter_increment_summable
    (G : GeometricExactResponseControl D L) :
    Summable fun n : ℕ =>
      |D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n| :=
  BernoulliGeometryBetaIncrementDecomposition.abs_parameter_increment_summable
    L.toBernoulliGeometryBetaIncrementDecomposition
    G.toGeometricGeometryBetaControl

/-- The exact coupling and geometry response estimates imply weak convergence
of the complete embedded plaquette-law sequence. -/
theorem fullWeakConvergence
    (G : GeometricExactResponseControl D L) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  BernoulliGeometryBetaIncrementDecomposition.fullWeakConvergence
    L.toBernoulliGeometryBetaIncrementDecomposition
    G.toGeometricGeometryBetaControl

/-- The finite-volume plaquette parameter converges to the canonical continuum
Bernoulli parameter under the exact response estimates. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (G : GeometricExactResponseControl D L) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  BernoulliGeometryBetaIncrementDecomposition.embeddedBernoulliParameter_tendsto_prokhorov
    L.toBernoulliGeometryBetaIncrementDecomposition
    G.toGeometricGeometryBetaControl

/-- Every convergent strict subsequence has the canonical weak limit under the
same exact response estimates. -/
theorem clusterPoint_eq_prokhorov
    (G : GeometricExactResponseControl D L)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure :=
  BernoulliGeometryBetaIncrementDecomposition.clusterPoint_eq_prokhorov
    L.toBernoulliGeometryBetaIncrementDecomposition
    G.toGeometricGeometryBetaControl f hf μ hμ

end GeometricExactResponseControl

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
