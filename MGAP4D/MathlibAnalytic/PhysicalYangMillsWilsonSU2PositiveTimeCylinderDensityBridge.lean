import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Topology

noncomputable section

private theorem positiveTimeCylinderDensityBridgeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveTimeCylinderDensityBridgeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- A concrete positive-time gauge-invariant cylinder carrier can be used to
prove the raw actual-analysis closure statement without any surjectivity
assumption on the coherent positive-half pullback.

The two inputs are deliberately separated:

* `hLift` says every chosen cylinder approximant is the pullback of an actual
  positive-time gauge-invariant observable;
* `hApprox` is the target-specific sup-norm approximation statement.

The conclusion is exactly the closure hypothesis consumed by the existing
continuous-to-`L²` transfer theorem. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_carrier
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeCylinderDensityBridgeTwoRankPositive beta hbeta)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (carrier : Set
      (BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) 2) ℝ))
    (hLift : carrier ⊆ LinearMap.range (Q.positiveHalfPullback n))
    (hApprox :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c ∈ closure carrier) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  exact closure_mono hLift hApprox

/-- If an actual positive-time gauge-invariant cylinder carrier is dense in the
finite open-half sup-norm space and every one of its elements has an actual
positive-time pullback preimage, then every explicit raw actual-analysis Wilson
mode lies in the required pullback range closure.

This is density, not surjectivity: no exact preimage for the raw mode is
asserted or constructed. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_dense_carrier
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeCylinderDensityBridgeTwoRankPositive beta hbeta)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (carrier : Set
      (BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) 2) ℝ))
    (hDense : Dense carrier)
    (hLift : carrier ⊆ LinearMap.range (Q.positiveHalfPullback n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_carrier
    n k c carrier hLift
  rw [hDense.closure_eq]
  exact mem_univ _

/-- The same dense-cylinder input immediately reaches the already-established
actual open-half Haar `L²` closure.  This is the exact handoff point needed by
the closure-derived reconstructed-excitation theorem. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_dense_carrier
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeCylinderDensityBridgeTwoRankPositive beta hbeta)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (carrier : Set
      (BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) 2) ℝ))
    (hDense : Dense carrier)
    (hLift : carrier ⊆ LinearMap.range (Q.positiveHalfPullback n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  apply Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
  exact Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_dense_carrier
    n k c carrier hDense hLift

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
