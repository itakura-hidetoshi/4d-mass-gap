import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventMatrixElementAnalytic
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorQuadraticCoercive
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

universe u

/-- The canonical bounded ambient resolvent of a self-adjoint partially defined
real-Hilbert operator is self-adjoint at every point of its coercive gap.

The proof never promotes the forward operator to a bounded map.  Instead it
chooses actual-domain preimages for the two test vectors, uses formal symmetry
of the unbounded operator on that domain, and transports the identity back
through the bounded two-sided resolvent inverse. -/
theorem realLinearPMapAmbientResolventFamily_isSelfAdjoint_of_isSelfAdjoint
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    IsSelfAdjoint
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda) := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hAdj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hSelf
  have hFormal : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint hSelf.dense_domain
    rw [hAdj] at h
    exact h
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro y z
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda y with
    ⟨x, hxy, hFx⟩
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda z with
    ⟨w, hzw, hFw⟩
  have hShiftSymm :
      inner ℝ (realLinearPMapDomainShift A lambda x) (w : E) =
        inner ℝ (x : E) (realLinearPMapDomainShift A lambda w) := by
    change inner ℝ (A x - lambda • (x : E)) (w : E) =
      inner ℝ (x : E) (A w - lambda • (w : E))
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hFormal x w]
  change inner ℝ (F lambda y) z = inner ℝ y (F lambda z)
  calc
    inner ℝ (F lambda y) z =
        inner ℝ (x : E) (realLinearPMapDomainShift A lambda w) := by
      rw [hFx, hzw]
    _ = inner ℝ (realLinearPMapDomainShift A lambda x) (w : E) :=
      hShiftSymm.symm
    _ = inner ℝ y (F lambda z) := by
      rw [hxy, hFw]

/-- A coercive quadratic lower bound for the actual-domain operator implies
nonnegativity of every fixed-vector quadratic form of its bounded ambient
resolvent throughout the symmetric coercive gap.

For `y = (A - λI)x`, the resolvent quadratic form is exactly
`⟪x,(A-λI)x⟫`; the estimate `|λ| < c` leaves the positive margin
`c-λ > 0`. -/
theorem realLinearPMapAmbientResolventFamily_inner_nonneg_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (y : E) :
    0 ≤ inner ℝ
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda y)
      y := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda y with
    ⟨x, hxy, hFx⟩
  have hlambda' : lambda < c := lt_of_le_of_lt (le_abs_self lambda) hlambda
  have hq := hQuad x
  change 0 ≤ inner ℝ (F lambda y) y
  rw [hFx, ← hxy, real_inner_comm]
  change 0 ≤ inner ℝ (A x - lambda • (x : E)) (x : E)
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖(x : E)‖]

/-- Consequently every power of the bounded ambient resolvent has a
nonnegative quadratic form.  This is the reusable completed-resolvent power
positivity spine, now fed by actual-domain support-generator receipts. -/
theorem realLinearPMapAmbientResolventFamily_pow_inner_nonneg
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (n : ℕ)
    (u : E) :
    0 ≤ inner ℝ
      ((realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda ^ n) u)
      u := by
  exact
    realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda)
      (realLinearPMapAmbientResolventFamily_isSelfAdjoint_of_isSelfAdjoint
        A c hc hNorm hKer hSurj hSelf lambda hlambda)
      (realLinearPMapAmbientResolventFamily_inner_nonneg_of_quadratic_lower_bound
        A c hc hNorm hKer hSurj hQuad lambda hlambda)
      n u

/-- Open-set version of the completed-resolvent scalar derivative spine.
If `R' = R²` throughout an open set, then the `n`-th derivative of every
quadratic matrix element is exactly `n! ⟪R^(n+1)u,u⟫`. -/
theorem resolvent_quadratic_iteratedDerivWithin_eq_factorial_of_isOpen
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (s : Set ℝ)
    (hs : IsOpen s)
    (hres : ∀ {lambda : ℝ}, lambda ∈ s →
      HasDerivAt res (res lambda ^ 2) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda ∈ s)
    (u : E) :
    iteratedDerivWithin n
        (fun mu : ℝ => inner ℝ (res mu u) u)
        s lambda =
      (n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (fun mu : ℝ => inner ℝ (res mu u) u) s)
              s lambda =
            derivWithin
              (fun mu : ℝ =>
                (n.factorial : ℝ) * inner ℝ ((res mu ^ (n + 1)) u) u)
              s lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hstep :=
        resolvent_quadratic_factorialDerivativeStep_hasDerivAt
          res n (hres hlambda) u
      exact hstep.hasDerivWithinAt.derivWithin (hs.uniqueDiffOn lambda hlambda)

/-- Ordinary all-order scalar derivative formula on an arbitrary open
resolvent region. -/
theorem resolvent_quadratic_iteratedDeriv_eq_factorial_of_isOpen
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (s : Set ℝ)
    (hs : IsOpen s)
    (hres : ∀ {lambda : ℝ}, lambda ∈ s →
      HasDerivAt res (res lambda ^ 2) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda ∈ s)
    (u : E) :
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
      (n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u := by
  calc
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
        iteratedDerivWithin n
          (fun mu : ℝ => inner ℝ (res mu u) u) s lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := fun mu : ℝ => inner ℝ (res mu u) u)
        hs hlambda).symm
    _ = (n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u :=
      resolvent_quadratic_iteratedDerivWithin_eq_factorial_of_isOpen
        res s hs hres n hlambda u

/-- The diagonal specialization of the scalar matrix-element response added in
the previous analytic layer. -/
noncomputable def realLinearPMapAmbientResolventQuadraticAmplitude
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (u : E)
    (lambda : ℝ) : ℝ :=
  realLinearPMapAmbientResolventMatrixElement
    A c hc hNorm hKer hSurj u u lambda

@[simp]
theorem realLinearPMapAmbientResolventQuadraticAmplitude_apply
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (u : E)
    (lambda : ℝ) :
    realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u lambda =
      inner ℝ
        (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda u)
        u := by
  rw [realLinearPMapAmbientResolventQuadraticAmplitude,
    realLinearPMapAmbientResolventMatrixElement_apply, real_inner_comm]

/-- Exact all-order derivative formula for the support-resolvent quadratic
amplitude on the full symmetric coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (u : E)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    iteratedDeriv n
        (realLinearPMapAmbientResolventQuadraticAmplitude
          A c hc hNorm hKer hSurj u)
        lambda =
      (n.factorial : ℝ) * inner ℝ
        ((realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda ^ (n + 1)) u)
        u := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hlambda' : lambda ∈ Set.Ioo (-c) c := abs_lt.mp hlambda
  have hformula :=
    resolvent_quadratic_iteratedDeriv_eq_factorial_of_isOpen
      F (Set.Ioo (-c) c) isOpen_Ioo
      (fun {mu} hmu => by
        have habs : |mu| < c := abs_lt.mpr hmu
        have h0 := realLinearPMapAmbientResolventFamily_hasDerivAt
          A c hc hNorm hKer hSurj mu habs
        simpa only [F, pow_two] using h0)
      n hlambda' u
  have hq :
      realLinearPMapAmbientResolventQuadraticAmplitude
          A c hc hNorm hKer hSurj u =
        fun mu => inner ℝ (F mu u) u := by
    funext mu
    exact realLinearPMapAmbientResolventQuadraticAmplitude_apply
      A c hc hNorm hKer hSurj u mu
  rw [hq]
  simpa only [F] using hformula

/-- Every derivative of the quadratic support-resolvent amplitude is
nonnegative on the full coercive gap: the precise absolute-monotonicity
receipt. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_nonneg
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    0 ≤ iteratedDeriv n
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u)
      lambda := by
  rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    A c hc hNorm hKer hSurj u n lambda hlambda]
  exact mul_nonneg (by positivity)
    (realLinearPMapAmbientResolventFamily_pow_inner_nonneg
      A c hc hNorm hKer hSurj hSelf hQuad lambda hlambda (n + 1) u)

end

end MathlibAnalytic
end MGAP4D
