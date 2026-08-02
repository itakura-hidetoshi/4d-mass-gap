import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompressionGeneratorDefect
import MGAP4D.MathlibAnalytic.RealContinuousLinearOperatorExponentialSemigroupPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProduct

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Isometric adjoint compression commutes exactly with real scalar
multiplication of the ambient operator. -/
theorem realHilbertIsometricAdjointCompression_smul
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (r : ℝ) :
    realHilbertIsometricAdjointCompression A (r • T) =
      r • realHilbertIsometricAdjointCompression A T := by
  apply ContinuousLinearMap.ext
  intro x
  change realHilbertAdjointSynthesis A ((r • T) (A x)) =
    (r • realHilbertIsometricAdjointCompression A T) x
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    map_smul, realHilbertIsometricAdjointCompression_apply]

/-- The generator leakage scales linearly with the ambient operator. -/
theorem realHilbertIsometricAdjointCompressionGeneratorDefect_smul
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (r : ℝ) :
    realHilbertIsometricAdjointCompressionGeneratorDefect A (r • T) =
      r • realHilbertIsometricAdjointCompressionGeneratorDefect A T := by
  apply ContinuousLinearMap.ext
  intro x
  rw [realHilbertIsometricAdjointCompressionGeneratorDefect_apply,
    realHilbertIsometricAdjointCompression_smul,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,
    realHilbertIsometricAdjointCompressionGeneratorDefect_apply,
    map_smul, smul_sub]

/-- Failure of adjoint compression to preserve a product of two ambient
operators.  The right operator acts first. -/
noncomputable def
    realHilbertIsometricAdjointCompressionMultiplicativeDefect
    (A : F →ₗᵢ[ℝ] E)
    (S T : E →L[ℝ] E) :
    F →L[ℝ] F :=
  realHilbertIsometricAdjointCompression A (S * T) -
    realHilbertIsometricAdjointCompression A S *
      realHilbertIsometricAdjointCompression A T

/-- The product-compression defect factors exactly through the orthogonal
leakage of the right operator. -/
@[simp] theorem
    realHilbertIsometricAdjointCompressionMultiplicativeDefect_apply
    (A : F →ₗᵢ[ℝ] E)
    (S T : E →L[ℝ] E)
    (x : F) :
    realHilbertIsometricAdjointCompressionMultiplicativeDefect A S T x =
      realHilbertAdjointSynthesis A
        (S (realHilbertIsometricAdjointCompressionGeneratorDefect A T x)) := by
  unfold realHilbertIsometricAdjointCompressionMultiplicativeDefect
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    realHilbertIsometricAdjointCompression_apply,
    realHilbertIsometricAdjointCompression_apply,
    realHilbertIsometricAdjointCompression_apply,
    realHilbertIsometricAdjointCompressionGeneratorDefect_apply,
    ContinuousLinearMap.mul_apply, map_sub, map_sub,
    realHilbertIsometricAdjointCompression_apply]

/-- If the right ambient operator preserves the analyzed range, compression
is multiplicative against every left operator. -/
theorem
    realHilbertIsometricAdjointCompressionMultiplicativeDefect_eq_zero_of_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (S T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0) :
    realHilbertIsometricAdjointCompressionMultiplicativeDefect A S T = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [realHilbertIsometricAdjointCompressionMultiplicativeDefect_apply, hD]
  simp

/-- The second-moment compression curvature.  It measures the difference
between compressing the ambient square and squaring the compressed operator. -/
noncomputable def realHilbertIsometricAdjointCompressionSecondMomentDefect
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    F →L[ℝ] F :=
  realHilbertIsometricAdjointCompressionMultiplicativeDefect A T T

/-- Exact second-moment decomposition at operator level. -/
theorem realHilbertIsometricAdjointCompression_secondMoment_decomposition
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    realHilbertIsometricAdjointCompression A (T * T) =
      realHilbertIsometricAdjointCompression A T *
          realHilbertIsometricAdjointCompression A T +
        realHilbertIsometricAdjointCompressionSecondMomentDefect A T := by
  unfold realHilbertIsometricAdjointCompressionSecondMomentDefect
  unfold realHilbertIsometricAdjointCompressionMultiplicativeDefect
  abel

/-- For a symmetric ambient operator, the quadratic form of the second-moment
curvature is exactly the squared generator-leakage norm. -/
theorem
    realHilbertIsometricAdjointCompressionSecondMomentDefect_quadraticForm
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u v : E, inner ℝ (T u) v = inner ℝ u (T v))
    (x : F) :
    inner ℝ
        (realHilbertIsometricAdjointCompressionSecondMomentDefect A T x) x =
      inner ℝ
        (realHilbertIsometricAdjointCompressionGeneratorDefect A T x)
        (realHilbertIsometricAdjointCompressionGeneratorDefect A T x) := by
  let K := realHilbertIsometricAdjointCompression A T
  let D := realHilbertIsometricAdjointCompressionGeneratorDefect A T
  have hK : ∀ u v : F, inner ℝ (K u) v = inner ℝ u (K v) :=
    realHilbertIsometricAdjointCompression_inner_symm A T hT
  have hEnergy :=
    realHilbertIsometricAdjointCompressionGeneratorDefect_inner_self_decomposition
      A T x
  change
    inner ℝ
      ((realHilbertIsometricAdjointCompression A (T * T) - K * K) x) x =
      inner ℝ (D x) (D x)
  rw [ContinuousLinearMap.sub_apply, inner_sub_left,
    realHilbertIsometricAdjointCompression_inner,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [hT (T (A x)) (A x), hK (K x) x]
  linarith

/-- The second-moment curvature is nonnegative for every symmetric ambient
operator. -/
theorem
    realHilbertIsometricAdjointCompressionSecondMomentDefect_nonneg
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u v : E, inner ℝ (T u) v = inner ℝ u (T v))
    (x : F) :
    0 ≤ inner ℝ
      (realHilbertIsometricAdjointCompressionSecondMomentDefect A T x) x := by
  rw [realHilbertIsometricAdjointCompressionSecondMomentDefect_quadraticForm
    A T hT x]
  exact real_inner_self_nonneg

/-- For a symmetric ambient operator, exact preservation of the second moment
is equivalent to vanishing of the complete generator leakage. -/
theorem
    realHilbertIsometricAdjointCompressionSecondMomentDefect_eq_zero_iff_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u v : E, inner ℝ (T u) v = inner ℝ u (T v)) :
    realHilbertIsometricAdjointCompressionSecondMomentDefect A T = 0 ↔
      realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0 := by
  constructor
  · intro hQ
    rw [realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff_inner_self]
    intro x
    have hx :
        inner ℝ
          (realHilbertIsometricAdjointCompressionSecondMomentDefect A T x) x = 0 := by
      rw [hQ]
      simp
    rwa [realHilbertIsometricAdjointCompressionSecondMomentDefect_quadraticForm
      A T hT x] at hx
  · intro hD
    exact
      realHilbertIsometricAdjointCompressionMultiplicativeDefect_eq_zero_of_generatorDefect_eq_zero
        A T T hD

/-- A single nonzero leakage witness forces nonzero second-moment curvature. -/
theorem
    realHilbertIsometricAdjointCompressionSecondMomentDefect_ne_zero_of_generatorDefect_apply_ne_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u v : E, inner ℝ (T u) v = inner ℝ u (T v))
    (x : F)
    (hx : realHilbertIsometricAdjointCompressionGeneratorDefect A T x ≠ 0) :
    realHilbertIsometricAdjointCompressionSecondMomentDefect A T ≠ 0 := by
  intro hQ
  have hD :=
    (realHilbertIsometricAdjointCompressionSecondMomentDefect_eq_zero_iff_generatorDefect_eq_zero
      A T hT).mp hQ
  exact hx (by rw [hD]; simp)

/-- Zero generator leakage remains zero after scaling the generator by time. -/
theorem
    realHilbertIsometricAdjointCompressionGeneratorDefect_smul_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (t : ℝ) :
    realHilbertIsometricAdjointCompressionGeneratorDefect A (t • T) = 0 := by
  rw [realHilbertIsometricAdjointCompressionGeneratorDefect_smul, hD,
    smul_zero]

/-- Zero generator leakage intertwines every power after arbitrary real-time
scaling of the ambient and compressed generators. -/
theorem
    realHilbertIsometricAdjointCompression_smul_pow_analysis_apply_of_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (t : ℝ)
    (m : ℕ)
    (x : F) :
    ((t • T) ^ m) (A x) =
      A (((t • realHilbertIsometricAdjointCompression A T) ^ m) x) := by
  have hScaled :
      realHilbertIsometricAdjointCompressionGeneratorDefect A (t • T) = 0 :=
    realHilbertIsometricAdjointCompressionGeneratorDefect_smul_eq_zero
      A T hD t
  have hPow :=
    realHilbertIsometricAdjointCompression_pow_analysis_apply_of_defect_eq_zero
      A (t • T) hScaled m x
  rw [realHilbertIsometricAdjointCompression_smul A T t] at hPow
  exact hPow

set_option maxHeartbeats 2000000 in
/-- Vanishing generator leakage upgrades all natural-power intertwining to
exact operator-exponential intertwining at every real time. -/
theorem
    realHilbertIsometricAdjointCompression_exponential_analysis_apply_of_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (t : ℝ)
    (x : F) :
    NormedSpace.exp (t • T) (A x) =
      A (NormedSpace.exp
        (t • realHilbertIsometricAdjointCompression A T) x) := by
  let K := realHilbertIsometricAdjointCompression A T
  have hAmbientMem :
      t • T ∈ Metric.eball (0 : E →L[ℝ] E)
        (NormedSpace.expSeries ℝ (E →L[ℝ] E)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hAmbientSum :
      HasSum
        (fun m : ℕ => ((Nat.factorial m : ℝ)⁻¹) • (t • T) ^ m)
        (NormedSpace.exp (t • T)) :=
    NormedSpace.expSeries_hasSum_exp_of_mem_ball' (t • T) hAmbientMem
  have hAmbientApply :
      HasSum
        (fun m : ℕ =>
          (((Nat.factorial m : ℝ)⁻¹) • (t • T) ^ m) (A x))
        (NormedSpace.exp (t • T) (A x)) :=
    (ContinuousLinearMap.apply ℝ E (A x)).hasSum hAmbientSum
  have hBoundaryMem :
      t • K ∈ Metric.eball (0 : F →L[ℝ] F)
        (NormedSpace.expSeries ℝ (F →L[ℝ] F)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hBoundarySum :
      HasSum
        (fun m : ℕ => ((Nat.factorial m : ℝ)⁻¹) • (t • K) ^ m)
        (NormedSpace.exp (t • K)) :=
    NormedSpace.expSeries_hasSum_exp_of_mem_ball' (t • K) hBoundaryMem
  have hBoundaryApply :
      HasSum
        (fun m : ℕ =>
          (((Nat.factorial m : ℝ)⁻¹) • (t • K) ^ m) x)
        (NormedSpace.exp (t • K) x) :=
    (ContinuousLinearMap.apply ℝ F x).hasSum hBoundarySum
  have hBoundaryAnalysis :
      HasSum
        (fun m : ℕ =>
          A ((((Nat.factorial m : ℝ)⁻¹) • (t • K) ^ m) x))
        (A (NormedSpace.exp (t • K) x)) :=
    A.toContinuousLinearMap.hasSum hBoundaryApply
  have hTerms (m : ℕ) :
      (((Nat.factorial m : ℝ)⁻¹) • (t • T) ^ m) (A x) =
        A ((((Nat.factorial m : ℝ)⁻¹) • (t • K) ^ m) x) := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      map_smul]
    exact congrArg
      (fun y : E => (Nat.factorial m : ℝ)⁻¹ • y)
      (realHilbertIsometricAdjointCompression_smul_pow_analysis_apply_of_generatorDefect_eq_zero
        A T hD t m x)
  apply HasSum.unique hAmbientApply
  exact hBoundaryAnalysis.congr fun m => (hTerms m).symm

/-- Under zero generator leakage, compressing the ambient exponential gives
exactly the exponential of the compressed generator. -/
theorem
    realHilbertIsometricAdjointCompression_exponential_of_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (t : ℝ) :
    realHilbertIsometricAdjointCompression A (NormedSpace.exp (t • T)) =
      NormedSpace.exp
        (t • realHilbertIsometricAdjointCompression A T) := by
  apply realHilbertIsometricAdjointCompression_eq_of_intertwines
  intro x
  exact
    realHilbertIsometricAdjointCompression_exponential_analysis_apply_of_generatorDefect_eq_zero
      A T hD t x

/-- Zero generator leakage implies analyzed-range invariance of every time
slice of the ambient exponential family. -/
theorem
    realHilbertIsometricAdjointCompression_exponential_rangeInvariant_of_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (t : ℝ) :
    realHilbertIsometricAdjointCompressionGeneratorRangeInvariant A
      (NormedSpace.exp (t • T)) := by
  intro x
  refine ⟨NormedSpace.exp
    (t • realHilbertIsometricAdjointCompression A T) x, ?_⟩
  exact
    realHilbertIsometricAdjointCompression_exponential_analysis_apply_of_generatorDefect_eq_zero
      A T hD t x

/-- Compression of a zero-defect exponential family is an honest additive
one-parameter semigroup. -/
theorem
    realHilbertIsometricAdjointCompression_exponential_add_of_generatorDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (s t : ℝ) :
    realHilbertIsometricAdjointCompression A (NormedSpace.exp ((s + t) • T)) =
      realHilbertIsometricAdjointCompression A (NormedSpace.exp (s • T)) *
        realHilbertIsometricAdjointCompression A (NormedSpace.exp (t • T)) := by
  rw [realHilbertIsometricAdjointCompression_exponential_of_generatorDefect_eq_zero
      A T hD (s + t),
    realHilbertIsometricAdjointCompression_exponential_of_generatorDefect_eq_zero
      A T hD s,
    realHilbertIsometricAdjointCompression_exponential_of_generatorDefect_eq_zero
      A T hD t]
  exact realContinuousLinearOperatorExponentialSemigroup_add
    (realHilbertIsometricAdjointCompression A T) s t

end

end MathlibAnalytic
end MGAP4D
