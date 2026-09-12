import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventAnalyticHierarchy
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

universe u

/-- Power-norm estimate in a normed ring under the weaker hypothesis
`‖1‖ ≤ 1`.  Unlike the standard `norm_pow_le`, this does not require a
`NormOneClass`; that distinction matters for continuous endomorphisms of a
possibly zero-dimensional normed space. -/
theorem norm_pow_le_of_norm_one_le_mgap
    {B : Type*}
    [NormedRing B]
    (hone : ‖(1 : B)‖ ≤ 1)
    (x : B)
    (n : ℕ) :
    ‖x ^ n‖ ≤ ‖x‖ ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using hone
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        ‖x ^ n * x‖ ≤ ‖x ^ n‖ * ‖x‖ := norm_mul_le _ _
        _ ≤ ‖x‖ ^ n * ‖x‖ :=
          mul_le_mul_of_nonneg_right ih (norm_nonneg x)

/-- Generic exact finite Taylor remainder for a resolvent identity.
If `Rμ - Rλ = h • (Rμ * Rλ)`, then after subtracting the first `n`
Neumann-Taylor coefficients the remainder is exactly
`h^n • (Rμ * Rλ^n)`.  This formulation needs no inverse operation and is
therefore particularly well suited to the actual-domain resolvent spine. -/
theorem resolvent_taylorRemainder_eq_of_sub_eq_smul_mul
    {B : Type*}
    [Ring B]
    [Algebra ℝ B]
    (Rmu Rlambda : B)
    (h : ℝ)
    (hid : Rmu - Rlambda = h • (Rmu * Rlambda))
    (n : ℕ) :
    Rmu - ∑ i ∈ Finset.range n, h ^ i • Rlambda ^ (i + 1) =
      h ^ n • (Rmu * Rlambda ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep :
          Rmu * Rlambda ^ n - Rlambda ^ (n + 1) =
            h • (Rmu * Rlambda ^ (n + 1)) := by
        calc
          Rmu * Rlambda ^ n - Rlambda ^ (n + 1) =
              (Rmu - Rlambda) * Rlambda ^ n := by
            rw [pow_succ', sub_mul]
          _ = (h • (Rmu * Rlambda)) * Rlambda ^ n := by rw [hid]
          _ = h • ((Rmu * Rlambda) * Rlambda ^ n) := by
            rw [smul_mul_assoc]
          _ = h • (Rmu * (Rlambda * Rlambda ^ n)) := by
            rw [mul_assoc]
          _ = h • (Rmu * Rlambda ^ (n + 1)) := by
            rw [← pow_succ']
      calc
        Rmu - ∑ i ∈ Finset.range (n + 1), h ^ i • Rlambda ^ (i + 1) =
            (Rmu - ∑ i ∈ Finset.range n, h ^ i • Rlambda ^ (i + 1)) -
              h ^ n • Rlambda ^ (n + 1) := by
          rw [Finset.sum_range_succ]
          abel
        _ = h ^ n • (Rmu * Rlambda ^ n) -
              h ^ n • Rlambda ^ (n + 1) := by rw [ih]
        _ = h ^ n •
              (Rmu * Rlambda ^ n - Rlambda ^ (n + 1)) := by
          module
        _ = h ^ n • (h • (Rmu * Rlambda ^ (n + 1))) := by
          rw [hstep]
        _ = h ^ (n + 1) • (Rmu * Rlambda ^ (n + 1)) := by
          simpa only [smul_smul, pow_succ]

/-- Exact finite Taylor-Neumann remainder for the canonical bounded ambient
support resolvent on the natural distance-to-boundary ball.  The forward
partially defined logarithmic generator is not promoted to a bounded map. -/
theorem realLinearPMapAmbientResolventFamily_taylorRemainder_eq
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (hh : |h| < c - |lambda|)
    (n : ℕ) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    F (lambda + h) -
        ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1) =
      h ^ n • (F (lambda + h) * F lambda ^ n) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hdist : |(lambda + h) - lambda| < c - |lambda| := by
    simpa using hh
  have hmu : |lambda + h| < c :=
    abs_lt_gap_of_abs_sub_lt_gap_sub_abs
      c lambda (lambda + h) hlambda hdist
  have hid0 := realLinearPMapAmbientResolventFamily_sub_eq_smul_comp
    A c hc hNorm hKer hSurj (lambda + h) lambda hmu hlambda
  have hid : F (lambda + h) - F lambda =
      h • (F (lambda + h) * F lambda) := by
    simpa only [F, add_sub_cancel_left] using hid0
  exact resolvent_taylorRemainder_eq_of_sub_eq_smul_mul
    (F (lambda + h)) (F lambda) h hid n

/-- Cauchy-type all-order operator-norm estimate for the support resolvent.
The distance `c - |λ|` to the coercive-gap boundary controls every derivative. -/
theorem realLinearPMapAmbientResolventFamily_iteratedDeriv_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖iteratedDeriv n F lambda‖ ≤
      (n.factorial : ℝ) * (c - |lambda|)⁻¹ ^ (n + 1) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hformula := realLinearPMapAmbientResolventFamily_iteratedDeriv_eq_factorial
    A c hc hNorm hKer hSurj n lambda hlambda
  have hF : ‖F lambda‖ ≤ (c - |lambda|)⁻¹ :=
    realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj lambda hlambda
  have hone : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro x
      simp
  have hpow : ‖F lambda ^ (n + 1)‖ ≤ ‖F lambda‖ ^ (n + 1) :=
    norm_pow_le_of_norm_one_le_mgap hone (F lambda) (n + 1)
  change ‖iteratedDeriv n F lambda‖ ≤
    (n.factorial : ℝ) * (c - |lambda|)⁻¹ ^ (n + 1)
  rw [hformula]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (n.factorial))]
  calc
    (n.factorial : ℝ) * ‖F lambda ^ (n + 1)‖ ≤
        (n.factorial : ℝ) * ‖F lambda‖ ^ (n + 1) := by
      gcongr
    _ ≤ (n.factorial : ℝ) * (c - |lambda|)⁻¹ ^ (n + 1) := by
      gcongr

/-- Quantitative bound for each Taylor-Neumann coefficient at a support
resolvent base point. -/
theorem realLinearPMapAmbientResolventFamily_taylorTerm_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (n : ℕ) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖h ^ n • F lambda ^ (n + 1)‖ ≤
      |h| ^ n * (c - |lambda|)⁻¹ ^ (n + 1) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hF : ‖F lambda‖ ≤ (c - |lambda|)⁻¹ :=
    realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj lambda hlambda
  have hone : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro x
      simp
  have hpow : ‖F lambda ^ (n + 1)‖ ≤ ‖F lambda‖ ^ (n + 1) :=
    norm_pow_le_of_norm_one_le_mgap hone (F lambda) (n + 1)
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    |h| ^ n * ‖F lambda ^ (n + 1)‖ ≤
        |h| ^ n * ‖F lambda‖ ^ (n + 1) := by
      gcongr
    _ ≤ |h| ^ n * (c - |lambda|)⁻¹ ^ (n + 1) := by
      gcongr

/-- Endpoint-sensitive finite Taylor remainder estimate.  It is obtained by
combining the exact remainder with the sharp one-point resolvent bounds at
`λ` and `λ+h`. -/
theorem realLinearPMapAmbientResolventFamily_taylorRemainder_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (hh : |h| < c - |lambda|)
    (n : ℕ) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖F (lambda + h) -
        ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1)‖ ≤
      |h| ^ n *
        ((c - |lambda + h|)⁻¹ * (c - |lambda|)⁻¹ ^ n) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hdist : |(lambda + h) - lambda| < c - |lambda| := by
    simpa using hh
  have hmu : |lambda + h| < c :=
    abs_lt_gap_of_abs_sub_lt_gap_sub_abs
      c lambda (lambda + h) hlambda hdist
  have hFmu : ‖F (lambda + h)‖ ≤ (c - |lambda + h|)⁻¹ :=
    realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj (lambda + h) hmu
  have hFlambda : ‖F lambda‖ ≤ (c - |lambda|)⁻¹ :=
    realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj lambda hlambda
  have hone : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro x
      simp
  have hpow : ‖F lambda ^ n‖ ≤ ‖F lambda‖ ^ n :=
    norm_pow_le_of_norm_one_le_mgap hone (F lambda) n
  have hmuInvNonneg : 0 ≤ (c - |lambda + h|)⁻¹ :=
    (inv_pos.mpr (sub_pos.mpr hmu)).le
  change ‖F (lambda + h) -
      ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1)‖ ≤
    |h| ^ n * ((c - |lambda + h|)⁻¹ * (c - |lambda|)⁻¹ ^ n)
  rw [realLinearPMapAmbientResolventFamily_taylorRemainder_eq
    A c hc hNorm hKer hSurj lambda h hlambda hh n]
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    |h| ^ n * ‖F (lambda + h) * F lambda ^ n‖ ≤
        |h| ^ n * (‖F (lambda + h)‖ * ‖F lambda ^ n‖) := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ |h| ^ n * (‖F (lambda + h)‖ * ‖F lambda‖ ^ n) := by
      gcongr
    _ ≤ |h| ^ n *
        ((c - |lambda + h|)⁻¹ * (c - |lambda|)⁻¹ ^ n) := by
      gcongr <;> assumption

/-- Distance-to-boundary-only Taylor remainder estimate.  The denominator
`c - |λ| - |h|` is positive exactly on the natural Neumann ball, and the
estimate exhibits the geometric decay of finite Taylor truncations. -/
theorem realLinearPMapAmbientResolventFamily_taylorRemainder_norm_le_gap
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda h : ℝ)
    (hlambda : |lambda| < c)
    (hh : |h| < c - |lambda|)
    (n : ℕ) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖F (lambda + h) -
        ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1)‖ ≤
      |h| ^ n *
        ((c - |lambda| - |h|)⁻¹ * (c - |lambda|)⁻¹ ^ n) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hbase := realLinearPMapAmbientResolventFamily_taylorRemainder_norm_le
    A c hc hNorm hKer hSurj lambda h hlambda hh n
  have htri : |lambda + h| ≤ |lambda| + |h| := abs_add_le _ _
  have hinner : 0 < c - |lambda| - |h| := by linarith
  have hcompare : c - |lambda| - |h| ≤ c - |lambda + h| := by
    linarith
  have hinv : (c - |lambda + h|)⁻¹ ≤ (c - |lambda| - |h|)⁻¹ :=
    inv_anti₀ hinner hcompare
  have hlambdaInvNonneg : 0 ≤ (c - |lambda|)⁻¹ :=
    (inv_pos.mpr (sub_pos.mpr hlambda)).le
  have hlambdaInvPowNonneg : 0 ≤ (c - |lambda|)⁻¹ ^ n :=
    pow_nonneg hlambdaInvNonneg n
  change ‖F (lambda + h) -
      ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1)‖ ≤
    |h| ^ n * ((c - |lambda| - |h|)⁻¹ * (c - |lambda|)⁻¹ ^ n)
  calc
    ‖F (lambda + h) -
        ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1)‖ ≤
      |h| ^ n * ((c - |lambda + h|)⁻¹ * (c - |lambda|)⁻¹ ^ n) := by
        simpa only [F] using hbase
    _ ≤ |h| ^ n *
        ((c - |lambda| - |h|)⁻¹ * (c - |lambda|)⁻¹ ^ n) := by
      gcongr <;> assumption

/-- Audit-visible quantitative analytic package for the bounded support
resolvent.  It records the all-order Cauchy bound together with exact and
norm-controlled Taylor remainders. -/
structure RealLinearPMapAmbientResolventQuantitativeAnalyticPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) : Prop where
  iteratedDerivNorm :
    ∀ n lambda, |lambda| < c →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      ‖iteratedDeriv n F lambda‖ ≤
        (n.factorial : ℝ) * (c - |lambda|)⁻¹ ^ (n + 1)
  exactTaylorRemainder :
    ∀ lambda h n, |lambda| < c → |h| < c - |lambda| →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      F (lambda + h) -
          ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1) =
        h ^ n • (F (lambda + h) * F lambda ^ n)
  taylorRemainderNorm :
    ∀ lambda h n, |lambda| < c → |h| < c - |lambda| →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      ‖F (lambda + h) -
          ∑ i ∈ Finset.range n, h ^ i • F lambda ^ (i + 1)‖ ≤
        |h| ^ n *
          ((c - |lambda| - |h|)⁻¹ * (c - |lambda|)⁻¹ ^ n)

/-- Construct the quantitative support-resolvent analytic package. -/
theorem realLinearPMapAmbientResolventQuantitativeAnalyticPackage
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    RealLinearPMapAmbientResolventQuantitativeAnalyticPackage
      A c hc hNorm hKer hSurj := by
  refine ⟨?_, ?_, ?_⟩
  · intro n lambda hlambda
    exact realLinearPMapAmbientResolventFamily_iteratedDeriv_norm_le
      A c hc hNorm hKer hSurj n lambda hlambda
  · intro lambda h n hlambda hh
    exact realLinearPMapAmbientResolventFamily_taylorRemainder_eq
      A c hc hNorm hKer hSurj lambda h hlambda hh n
  · intro lambda h n hlambda hh
    exact realLinearPMapAmbientResolventFamily_taylorRemainder_norm_le_gap
      A c hc hNorm hKer hSurj lambda h hlambda hh n

end

end MathlibAnalytic
end MGAP4D