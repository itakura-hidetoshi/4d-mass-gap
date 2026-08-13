import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonGramFactorizedOperatorLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonality
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

private theorem cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance cyclicFourEdgeWilsonGramStrictnessLimitSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeWilsonGramStrictnessLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonGramStrictnessLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonGramStrictnessLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonGramStrictnessLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonGramStrictnessLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonGramStrictnessLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Operator-norm convergence of the finite full-residual Gram factors implies
convergence of every fixed quadratic form.

The evaluation map `(T,f) ↦ T f` is bounded bilinear, and the real Hilbert
inner product is continuous, so no coordinate expansion or scalar probe is
needed. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedQuadratic_tendsto_actual
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    Tendsto
      (fun degree =>
        inner ℝ
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
            H hH beta hbeta degree f)
          f)
      atTop
      (𝓝
        (inner ℝ
          (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
            H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta f)
          f)) := by
  let X := Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)
  let Gd := fun degree =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
      H hH beta hbeta degree
  let G := periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
    H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta
  have hG : Tendsto Gd atTop (𝓝 G) := by
    simpa [Gd, G] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator_tendsto_actual
        hH beta hbeta
  have hpair :
      Tendsto (fun degree => (Gd degree, f)) atTop (𝓝 (G, f)) :=
    hG.prodMk_nhds tendsto_const_nhds
  have happly : Tendsto (fun degree => Gd degree f) atTop (𝓝 (G f)) := by
    have hEval : Continuous (fun z : (X →L[ℝ] X) × X => z.1 z.2) :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := X) (F := X)).continuous
    exact (hEval.tendsto (G, f)).comp hpair
  simpa [Gd, G] using happly.inner tendsto_const_nhds

/-- A uniform strictly positive lower bound on the **positive finite Gram
quadratic forms** survives the Wilson/Fock limit and becomes a strict actual
`A†A` witness.  This replaces the previous signed scalar-probe lower-bound
interface by a cancellation-free one. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_of_eventually_partialFactorized_ge
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ᶠ degree in atTop,
      delta ≤ inner ℝ
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator
          H hH beta hbeta degree f)
        f) :
    0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta f)
      f := by
  have hlimit :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedQuadratic_tendsto_actual
      hH beta hbeta f
  exact lt_of_lt_of_le hdelta (ge_of_tendsto hlimit hlower)

/-- Equivalent finite-analysis formulation of the preceding theorem: an
eventual positive lower bound on `‖A_degree f‖²` yields a strict actual Gram
quadratic form.  Every finite quantity in the assumption is nonnegative by
construction. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_of_eventually_partialAnalysis_norm_sq_ge
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ᶠ degree in atTop,
      delta ≤
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
          H hH beta hbeta degree f‖ ^ 2) :
    0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta f)
      f := by
  apply
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_of_eventually_partialFactorized_ge
      hH beta hbeta f delta hdelta
  filter_upwards [hlower] with degree hdegree
  simpa only [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialFactorizedOperator_inner_self] using
    hdegree

/-- Cancellation-free finite Gram control therefore proves that the genuine
completed-positive Wilson analysis output is nonzero. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_ne_zero_of_eventually_partialAnalysis_norm_sq_ge
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ᶠ degree in atTop,
      delta ≤
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
          H hH beta hbeta degree f‖ ^ 2) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta f ≠ 0 := by
  have hpos :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_of_eventually_partialAnalysis_norm_sq_ge
      hH beta hbeta f delta hdelta hlower
  exact
    (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_iff_analysis_ne_zero
      H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta f).mp hpos

/-- For a centered interacting-boundary trace polynomial, the same positive
finite-Gram lower bound yields a genuine nonzero **vacuum-orthogonal** actual
open-half state.  This is the exact Hilbert-space output required by the
physical excitation route. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered_and_ne_zero_of_eventually_partialAnalysis_norm_sq_ge
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          H beta hbeta k c) = 0)
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ᶠ degree in atTop,
      delta ≤
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
          H hH beta hbeta degree
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta k c)‖ ^ 2) :
    inner ℝ
        (periodicHypercubicEvenOpenHalfConstantOneL2 H 2)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta k c)) = 0 ∧
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFourEdgeWilsonGramStrictnessLimitTwoRankPositive beta hbeta
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta k c) ≠ 0 := by
  constructor
  · exact
      periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered
        H beta hbeta k c hzero
  · exact
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_ne_zero_of_eventually_partialAnalysis_norm_sq_ge
        hH beta hbeta
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta k c)
        delta hdelta hlower

end

end MathlibAnalytic
end MGAP4D
