import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveProductL2Limit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryGramFactorization
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelGramFactorizationContinuity
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasureInstances
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

private theorem cyclicFourEdgeWilsonGramFactorLimitTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance cyclicFourEdgeWilsonGramFactorLimitSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeWilsonGramFactorLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonGramFactorLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonGramFactorLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonGramFactorLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonGramFactorLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonGramFactorLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance cyclicFourEdgeWilsonGramFactorLimitBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance cyclicFourEdgeWilsonGramFactorLimitOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- Canonical positive Gram operator attached to the complete finite
four-edge Wilson/Fock rectangular kernel.  The residual completed-positive
factor is kept exact; only the four distinguished temporal Wilson factors are
Taylor/Fock truncated. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
  realL2HilbertSchmidtRectangularKernelFactorizedOperator
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2
      H hH beta hbeta degree)

/-- Every finite full-residual Wilson/Fock Gram quadratic form is exactly the
squared norm of its rectangular analysis vector.  In particular there is no
signed scalar-probe cancellation at this level. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator_inner_self
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
          H hH beta hbeta degree f) f =
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
          H hH beta hbeta degree f‖ ^ 2 := by
  simpa [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator] using
    realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2
        H hH beta hbeta degree) f

/-- Finite Gram strictness is exactly finite actual-analysis nonvanishing. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator_inner_self_pos_iff
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    0 < inner ℝ
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
          H hH beta hbeta degree f) f ↔
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
          H hH beta hbeta degree f ≠ 0 := by
  simpa [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator] using
    realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self_pos_iff
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2
        H hH beta hbeta degree) f

/-- The complete finite full-residual Wilson/Fock Gram operators converge in
operator norm to the actual completed-positive Wilson operator `A†A`.

This is the cancellation-free operator-level limit needed to pass finite Fock
strictness to the actual analysis sector: no residual interaction is replaced
by `1`, and no non-diagonal Fock sector is discarded. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator_tendsto_actual
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
          H hH beta hbeta degree)
      atTop
      (𝓝
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 cyclicFourEdgeWilsonGramFactorLimitTwoRankPositive beta hbeta)) := by
  have hK :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2_tendsto_actual
      hH beta hbeta
  have hG :=
    realL2HilbertSchmidtRectangularKernelFactorizedOperator_tendsto
      (μ := periodicHypercubicEvenBoundaryHaarMeasure H 2)
      (ν := periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      hK
  simpa [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_eq_generic] using hG

end

end MathlibAnalytic
end MGAP4D
