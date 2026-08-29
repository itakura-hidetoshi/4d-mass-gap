import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventQuantitativeAnalyticBounds
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

universe u

/-- The real matrix-element functional on bounded endomorphisms. It first
applies the bounded operator to `x`, then pairs with `y`. -/
noncomputable def continuousLinearMapRealMatrixElement
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (x y : E) :
    (E →L[ℝ] E) →L[ℝ] ℝ :=
  (innerSL ℝ y).comp ((ContinuousLinearMap.apply ℝ E) x)

@[simp]
theorem continuousLinearMapRealMatrixElement_apply
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (x y : E)
    (T : E →L[ℝ] E) :
    continuousLinearMapRealMatrixElement x y T = ⟪y, T x⟫_ℝ :=
  rfl

/-- Cauchy--Schwarz plus the operator norm controls every real matrix
element of a bounded endomorphism. -/
theorem abs_continuousLinearMapRealMatrixElement_le
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (x y : E)
    (T : E →L[ℝ] E) :
    |continuousLinearMapRealMatrixElement x y T| ≤
      ‖y‖ * (‖T‖ * ‖x‖) := by
  rw [continuousLinearMapRealMatrixElement_apply]
  calc
    |⟪y, T x⟫_ℝ| ≤ ‖y‖ * ‖T x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖x‖) := by
      gcongr
      exact T.le_opNorm x

/-- Scalar matrix-element response of the canonical bounded ambient
resolvent associated with a coercive partially defined real-linear operator. -/
noncomputable def realLinearPMapAmbientResolventMatrixElement
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E)
    (lambda : ℝ) : ℝ :=
  continuousLinearMapRealMatrixElement x y
    (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda)

@[simp]
theorem realLinearPMapAmbientResolventMatrixElement_apply
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E)
    (lambda : ℝ) :
    realLinearPMapAmbientResolventMatrixElement
      A c hc hNorm hKer hSurj x y lambda =
      ⟪y,
        (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda) x⟫_ℝ :=
  rfl

/-- Every scalar matrix element inherits local real analyticity from the
operator-norm analytic bounded resolvent family. -/
theorem realLinearPMapAmbientResolventMatrixElement_analyticAt
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    AnalyticAt ℝ
      (realLinearPMapAmbientResolventMatrixElement
        A c hc hNorm hKer hSurj x y)
      lambda := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let M := continuousLinearMapRealMatrixElement x y
  have hF : AnalyticAt ℝ F lambda :=
    realLinearPMapAmbientResolventFamily_analyticAt
      A c hc hNorm hKer hSurj lambda hlambda
  have hM : AnalyticAt ℝ M (F lambda) := M.analyticAt (F lambda)
  simpa [realLinearPMapAmbientResolventMatrixElement, F, M] using
    (AnalyticAt.comp'
      (𝕜 := ℝ)
      (g := M)
      (f := F)
      hM hF)

/-- Matrix elements are analytic throughout the full open coercive gap. -/
theorem realLinearPMapAmbientResolventMatrixElement_analyticOnNhd
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E) :
    AnalyticOnNhd ℝ
      (realLinearPMapAmbientResolventMatrixElement
        A c hc hNorm hKer hSurj x y)
      {lambda : ℝ | |lambda| < c} := by
  intro lambda hlambda
  exact realLinearPMapAmbientResolventMatrixElement_analyticAt
    A c hc hNorm hKer hSurj x y lambda hlambda

/-- Exact scalar Taylor--Neumann series on the natural distance-to-boundary
ball, obtained by applying a continuous linear functional to the operator
series. -/
theorem realLinearPMapAmbientResolventMatrixElement_hasSum_taylorNeumann
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (hh : |h| < c - |lambda|) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    HasSum
      (fun n : ℕ => h ^ n * ⟪y, (F lambda ^ (n + 1)) x⟫_ℝ)
      ⟪y, F (lambda + h) x⟫_ℝ := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let M := continuousLinearMapRealMatrixElement x y
  have hs := realLinearPMapAmbientResolventFamily_hasSum_taylorNeumann
    A c hc hNorm hKer hSurj lambda h hlambda hh
  have hm := M.hasSum hs
  simpa [M, continuousLinearMapRealMatrixElement, F] using hm

/-- Exact finite scalar Taylor remainder. -/
theorem realLinearPMapAmbientResolventMatrixElement_taylorRemainder_eq
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (hh : |h| < c - |lambda|)
    (n : ℕ) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ⟪y, F (lambda + h) x⟫_ℝ -
        ∑ i ∈ Finset.range n,
          h ^ i * ⟪y, (F lambda ^ (i + 1)) x⟫_ℝ =
      h ^ n * ⟪y, (F (lambda + h) * F lambda ^ n) x⟫_ℝ := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let M := continuousLinearMapRealMatrixElement x y
  have hop := realLinearPMapAmbientResolventFamily_taylorRemainder_eq
    A c hc hNorm hKer hSurj lambda h hlambda hh n
  have hm := congrArg M hop
  simpa [M, continuousLinearMapRealMatrixElement, F,
    inner_sub_right, inner_sum, real_inner_smul_right] using hm

/-- Quantitative scalar Taylor remainder obtained from the exact operator
remainder estimate and Cauchy--Schwarz. -/
theorem realLinearPMapAmbientResolventMatrixElement_taylorRemainder_abs_le
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (hh : |h| < c - |lambda|)
    (n : ℕ) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    |⟪y, F (lambda + h) x⟫_ℝ -
        ∑ i ∈ Finset.range n,
          h ^ i * ⟪y, (F lambda ^ (i + 1)) x⟫_ℝ| ≤
      ‖y‖ *
        (|h| ^ n *
          ((c - |lambda| - |h|)⁻¹ *
            (c - |lambda|)⁻¹ ^ n) * ‖x‖) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  rw [realLinearPMapAmbientResolventMatrixElement_taylorRemainder_eq
    A c hc hNorm hKer hSurj x y lambda h hlambda hh n]
  rw [abs_mul, abs_pow]
  have hmatrix := abs_continuousLinearMapRealMatrixElement_le
    x y (F (lambda + h) * F lambda ^ n)
  rw [continuousLinearMapRealMatrixElement_apply] at hmatrix
  have hop := realLinearPMapAmbientResolventFamily_taylorRemainder_norm_le_gap
    A c hc hNorm hKer hSurj lambda h hlambda hh n
  have heq := realLinearPMapAmbientResolventFamily_taylorRemainder_eq
    A c hc hNorm hKer hSurj lambda h hlambda hh n
  dsimp only at hop heq
  rw [heq, norm_smul, Real.norm_eq_abs, abs_pow] at hop
  have hterm :
      |h| ^ n * ‖F (lambda + h) * F lambda ^ n‖ ≤
        |h| ^ n *
          ((c - |lambda| - |h|)⁻¹ * (c - |lambda|)⁻¹ ^ n) := by
    simpa [F] using hop
  calc
    |h| ^ n * |⟪y, (F (lambda + h) * F lambda ^ n) x⟫_ℝ| ≤
        |h| ^ n * (‖y‖ *
          (‖F (lambda + h) * F lambda ^ n‖ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left hmatrix (pow_nonneg (abs_nonneg h) n)
    _ = ‖y‖ *
        ((|h| ^ n * ‖F (lambda + h) * F lambda ^ n‖) * ‖x‖) := by
      ring
    _ ≤ ‖y‖ *
        ((|h| ^ n *
          ((c - |lambda| - |h|)⁻¹ * (c - |lambda|)⁻¹ ^ n)) * ‖x‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg y)
      exact mul_le_mul_of_nonneg_right hterm (norm_nonneg x)
    _ = ‖y‖ *
        (|h| ^ n *
          ((c - |lambda| - |h|)⁻¹ *
            (c - |lambda|)⁻¹ ^ n) * ‖x‖) := by
      ring

/-- Audit-visible scalar matrix-element analytic package. -/
structure RealLinearPMapAmbientResolventMatrixElementAnalyticPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E) : Prop where
  analyticOnGap :
    AnalyticOnNhd ℝ
      (realLinearPMapAmbientResolventMatrixElement
        A c hc hNorm hKer hSurj x y)
      {lambda : ℝ | |lambda| < c}
  taylorHasSum :
    ∀ lambda h, |lambda| < c → |h| < c - |lambda| →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      HasSum
        (fun n : ℕ => h ^ n * ⟪y, (F lambda ^ (n + 1)) x⟫_ℝ)
        ⟪y, F (lambda + h) x⟫_ℝ
  exactTaylorRemainder :
    ∀ lambda h n, |lambda| < c → |h| < c - |lambda| →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      ⟪y, F (lambda + h) x⟫_ℝ -
          ∑ i ∈ Finset.range n,
            h ^ i * ⟪y, (F lambda ^ (i + 1)) x⟫_ℝ =
        h ^ n * ⟪y, (F (lambda + h) * F lambda ^ n) x⟫_ℝ

/-- Construct the scalar matrix-element analytic package without adding any
boundedness hypothesis on the forward partially defined operator. -/
theorem realLinearPMapAmbientResolventMatrixElementAnalyticPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ z : A.domain, c * ‖(z : E)‖ ≤ ‖A z‖)
    (hKer : ∀ z : A.domain, A z = 0 → z = 0)
    (hSurj : Function.Surjective A.toFun)
    (x y : E) :
    RealLinearPMapAmbientResolventMatrixElementAnalyticPackage
      A c hc hNorm hKer hSurj x y := by
  refine ⟨?_, ?_, ?_⟩
  · exact realLinearPMapAmbientResolventMatrixElement_analyticOnNhd
      A c hc hNorm hKer hSurj x y
  · intro lambda h hlambda hh
    exact realLinearPMapAmbientResolventMatrixElement_hasSum_taylorNeumann
      A c hc hNorm hKer hSurj x y lambda h hlambda hh
  · intro lambda h n hlambda hh
    exact realLinearPMapAmbientResolventMatrixElement_taylorRemainder_eq
      A c hc hNorm hKer hSurj x y lambda h hlambda hh n

end

end MathlibAnalytic
end MGAP4D
