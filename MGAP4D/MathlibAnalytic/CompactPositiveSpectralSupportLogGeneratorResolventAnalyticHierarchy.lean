import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventHasDeriv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventTaylorNeumann
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

universe u

/-- Generic all-order resolvent derivative formula on an arbitrary open set.
This is the symmetric-gap version of the completed below-gap hierarchy: the
only input is the pointwise receipt `R' = R^2` on the open set. -/
theorem resolvent_iteratedDerivWithin_eq_factorial_of_isOpen
    {B : Type*}
    [NormedRing B]
    [NormedAlgebra ℝ B]
    (res : ℝ → B)
    (s : Set ℝ)
    (hs : IsOpen s)
    (hres : ∀ {lambda : ℝ}, lambda ∈ s →
      HasDerivAt res (res lambda ^ 2) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda ∈ s) :
    iteratedDerivWithin n res s lambda =
      (n.factorial : ℝ) • res lambda ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin (iteratedDerivWithin n res s) s lambda =
            derivWithin
              (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
              s lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hpow := resolvent_pow_hasDerivAt res (n + 1) (hres hlambda)
      have hscaledAt :
          HasDerivAt
            (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
            ((n.factorial : ℝ) •
              (((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2)))
            lambda := by
        simpa only [Pi.smul_apply] using
          (HasDerivAt.const_smul
            (𝕜 := ℝ) (R := ℝ) (F := B)
            (n.factorial : ℝ) hpow)
      have hscaledDeriv :
          derivWithin
              (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
              s lambda =
            (n.factorial : ℝ) •
              (((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2)) :=
        hscaledAt.hasDerivWithinAt.derivWithin (hs.uniqueDiffOn lambda hlambda)
      rw [hscaledDeriv]
      simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        smul_smul, mul_comm, Nat.add_assoc]

/-- Ordinary all-order derivative formula at interior points of an arbitrary
open set. -/
theorem resolvent_iteratedDeriv_eq_factorial_of_isOpen
    {B : Type*}
    [NormedRing B]
    [NormedAlgebra ℝ B]
    (res : ℝ → B)
    (s : Set ℝ)
    (hs : IsOpen s)
    (hres : ∀ {lambda : ℝ}, lambda ∈ s →
      HasDerivAt res (res lambda ^ 2) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda ∈ s) :
    iteratedDeriv n res lambda =
      (n.factorial : ℝ) • res lambda ^ (n + 1) := by
  calc
    iteratedDeriv n res lambda = iteratedDerivWithin n res s lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n) (f := res) hs hlambda).symm
    _ = (n.factorial : ℝ) • res lambda ^ (n + 1) :=
      resolvent_iteratedDerivWithin_eq_factorial_of_isOpen
        res s hs hres n hlambda

/-- The exact support-resolvent derivative values satisfy the factorial
recurrence `d(n! R^(n+1))/dλ = (n+1)! R^(n+2)` throughout the coercive gap. -/
theorem realLinearPMapAmbientResolventFamily_factorialDerivativeStep_hasDerivAt
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
    HasDerivAt
      (fun mu => (n.factorial : ℝ) • F mu ^ (n + 1))
      (((n + 1).factorial : ℝ) • F lambda ^ (n + 2))
      lambda := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hbase0 := realLinearPMapAmbientResolventFamily_hasDerivAt
    A c hc hNorm hKer hSurj lambda hlambda
  have hbase : HasDerivAt F (F lambda ^ 2) lambda := by
    simpa only [pow_two] using hbase0
  exact resolvent_factorialDerivativeStep_hasDerivAt F n hbase

/-- Exact `n`-th operator-norm derivative of the canonical ambient support
resolvent on the symmetric coercive gap. -/
theorem realLinearPMapAmbientResolventFamily_iteratedDeriv_eq_factorial
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
    iteratedDeriv n F lambda =
      (n.factorial : ℝ) • F lambda ^ (n + 1) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hlambda' : lambda ∈ Set.Ioo (-c) c := abs_lt.mp hlambda
  apply resolvent_iteratedDeriv_eq_factorial_of_isOpen
    F (Set.Ioo (-c) c) isOpen_Ioo
  · intro mu hmu
    have habs : |mu| < c := abs_lt.mpr hmu
    have h0 := realLinearPMapAmbientResolventFamily_hasDerivAt
      A c hc hNorm hKer hSurj mu habs
    simpa only [F, pow_two] using h0
  · exact hlambda'

/-- The natural distance-to-boundary radius implies the Neumann smallness
condition for the bounded ambient resolvent at the base point. -/
theorem realLinearPMapAmbientResolventFamily_neumannSmall_of_abs_sub_lt_gap
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
    (lambda mu : ℝ)
    (hlambda : |lambda| < c)
    (hmu : |mu - lambda| < c - |lambda|) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖(mu - lambda) • F lambda‖ < 1 := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hgap : 0 < c - |lambda| := sub_pos.mpr hlambda
  have hres : ‖F lambda‖ ≤ (c - |lambda|)⁻¹ :=
    realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj lambda hlambda
  calc
    ‖(mu - lambda) • F lambda‖ ≤ |mu - lambda| * ‖F lambda‖ := by
      simpa only [Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le (mu - lambda) (F lambda)
    _ ≤ |mu - lambda| * (c - |lambda|)⁻¹ :=
      mul_le_mul_of_nonneg_left hres (abs_nonneg _)
    _ < 1 := by
      rw [mul_inv_lt_iff₀ hgap]
      simpa only [one_mul] using hmu

/-- The natural distance-to-boundary ball stays inside the symmetric coercive
gap. -/
theorem abs_lt_gap_of_abs_sub_lt_gap_sub_abs
    (c lambda mu : ℝ)
    (hlambda : |lambda| < c)
    (hmu : |mu - lambda| < c - |lambda|) :
    |mu| < c := by
  have htri : |mu| ≤ |lambda| + |mu - lambda| := by
    calc
      |mu| = |lambda + (mu - lambda)| := by ring_nf
      _ ≤ |lambda| + |mu - lambda| := abs_add _ _
  linarith

/-- Exact local bounded-ring factorization of the support resolvent.  The
forward partially defined generator is absent: only two bounded resolvent
values and their exact resolvent identity are used. -/
theorem realLinearPMapAmbientResolventFamily_eq_mul_ringInverse_one_sub
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
    (lambda mu : ℝ)
    (hlambda : |lambda| < c)
    (hmu : |mu - lambda| < c - |lambda|) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    F mu = F lambda * Ring.inverse (1 - (mu - lambda) • F lambda) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let t := (mu - lambda) • F lambda
  have hmuGap : |mu| < c :=
    abs_lt_gap_of_abs_sub_lt_gap_sub_abs c lambda mu hlambda hmu
  have hid0 := realLinearPMapAmbientResolventFamily_sub_eq_smul_comp
    A c hc hNorm hKer hSurj mu lambda hmuGap hlambda
  have hid : F mu - F lambda = (mu - lambda) • (F mu * F lambda) := by
    simpa only [F] using hid0
  have ht : ‖t‖ < 1 := by
    simpa only [t, F] using
      realLinearPMapAmbientResolventFamily_neumannSmall_of_abs_sub_lt_gap
        A c hc hNorm hKer hSurj lambda mu hlambda hmu
  have htunit : IsUnit (1 - t) :=
    (Units.oneSub t ht).isUnit
  have hfactor : F mu * (1 - t) = F lambda := by
    rw [mul_sub, mul_one]
    have hmul : F mu * t = (mu - lambda) • (F mu * F lambda) := by
      dsimp [t]
      rw [Algebra.mul_smul_comm]
    rw [hmul, ← hid]
    abel
  calc
    F mu = F mu * 1 := by rw [mul_one]
    _ = F mu * ((1 - t) * Ring.inverse (1 - t)) := by
      rw [mul_ringInverse_eq_one_of_isUnit (1 - t) htunit]
    _ = (F mu * (1 - t)) * Ring.inverse (1 - t) := by
      rw [mul_assoc]
    _ = F lambda * Ring.inverse (1 - t) := by rw [hfactor]
    _ = F lambda * Ring.inverse (1 - (mu - lambda) • F lambda) := by
      rfl

/-- Left multiplication by a resolvent converts the geometric powers into the
Taylor coefficients `h^n R^(n+1)`. -/
theorem mul_smul_pow_eq_smul_pow_succ
    {R : Type*}
    [Ring R]
    [Algebra ℝ R]
    (h : ℝ)
    (x : R)
    (n : ℕ) :
    x * (h • x) ^ n = h ^ n • x ^ (n + 1) := by
  rw [smul_pow, Algebra.mul_smul_comm]
  simpa [pow_succ']

/-- Taylor-Neumann series for the canonical ambient support resolvent, with
operator-norm convergence on the full distance-to-boundary radius. -/
theorem realLinearPMapAmbientResolventFamily_hasSum_taylorNeumann
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
    (hh : |h| < c - |lambda|) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    HasSum
      (fun n : ℕ => h ^ n • F lambda ^ (n + 1))
      (F (lambda + h)) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let t := h • F lambda
  have hdist : |(lambda + h) - lambda| < c - |lambda| := by
    simpa using hh
  have ht : ‖t‖ < 1 := by
    simpa only [t, F] using
      realLinearPMapAmbientResolventFamily_neumannSmall_of_abs_sub_lt_gap
        A c hc hNorm hKer hSurj lambda (lambda + h) hlambda hdist
  have hsumm : Summable (fun n : ℕ => t ^ n) :=
    summable_geometric_of_norm_lt_one ht
  have hinvTsum : Ring.inverse (1 - t) = ∑' n : ℕ, t ^ n :=
    NormedRing.inverse_one_sub t ht
  have hgeom : HasSum (fun n : ℕ => t ^ n) (Ring.inverse (1 - t)) := by
    rw [hinvTsum]
    exact hsumm.hasSum
  have hfactor :=
    realLinearPMapAmbientResolventFamily_eq_mul_ringInverse_one_sub
      A c hc hNorm hKer hSurj lambda (lambda + h) hlambda hdist
  rw [hfactor]
  simpa only [t, F, mul_smul_pow_eq_smul_pow_succ] using
    hgeom.mul_left (F lambda)

/-- Local real analyticity of the canonical ambient support resolvent.  The
proof identifies it near each base point with a bounded-ring Neumann inverse;
no bounded forward generator is introduced. -/
theorem realLinearPMapAmbientResolventFamily_analyticAt
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
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    AnalyticAt ℝ
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj)
      lambda := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let R0 := F lambda
  let q : ℝ → (E →L[ℝ] E) := fun mu =>
    1 - (mu - lambda) • R0
  let candidate : ℝ → (E →L[ℝ] E) := fun mu =>
    R0 * Ring.inverse (q mu)
  have hsub : AnalyticAt ℝ (fun mu : ℝ => mu - lambda) lambda :=
    analyticAt_id.sub analyticAt_const
  have hR0 : AnalyticAt ℝ (fun _ : ℝ => R0) lambda := analyticAt_const
  have hsmul : AnalyticAt ℝ (fun mu : ℝ => (mu - lambda) • R0) lambda :=
    hsub.smul hR0
  have hq : AnalyticAt ℝ q lambda := by
    dsimp [q]
    exact analyticAt_const.sub hsmul
  have hq0 : q lambda = 1 := by simp [q]
  have hinverseAt : AnalyticAt ℝ Ring.inverse (q lambda) := by
    rw [hq0]
    simpa using
      (analyticAt_inverse (𝕜 := ℝ) (1 : (E →L[ℝ] E)ˣ))
  have hinverse : AnalyticAt ℝ (fun mu => Ring.inverse (q mu)) lambda :=
    AnalyticAt.comp'
      (𝕜 := ℝ)
      (g := fun z : E →L[ℝ] E => Ring.inverse z)
      (f := q)
      hinverseAt hq
  have hcandidate : AnalyticAt ℝ candidate lambda := by
    dsimp [candidate]
    exact hR0.mul hinverse
  have hgap : 0 < c - |lambda| := sub_pos.mpr hlambda
  have hopen : IsOpen {mu : ℝ | |mu - lambda| < c - |lambda|} :=
    isOpen_lt
      (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const
  have hmem : lambda ∈ {mu : ℝ | |mu - lambda| < c - |lambda|} := by
    simpa using hgap
  have heq : F =ᶠ[𝓝 lambda] candidate := by
    filter_upwards [hopen.mem_nhds hmem] with mu hmu
    dsimp [candidate, q, R0, F]
    exact realLinearPMapAmbientResolventFamily_eq_mul_ringInverse_one_sub
      A c hc hNorm hKer hSurj lambda mu hlambda hmu
  exact hcandidate.congr heq.symm

/-- Real analyticity on the whole open coercive gap. -/
theorem realLinearPMapAmbientResolventFamily_analyticOnNhd
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
    AnalyticOnNhd ℝ
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj)
      {lambda : ℝ | |lambda| < c} := by
  intro lambda hlambda
  exact realLinearPMapAmbientResolventFamily_analyticAt
    A c hc hNorm hKer hSurj lambda hlambda

/-- Audit-visible coherent package: all-order derivatives, Taylor-Neumann
expansion, and local real analyticity of the bounded ambient resolvent. -/
structure RealLinearPMapAmbientResolventAnalyticHierarchyPackage
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
  iteratedDerivFormula :
    ∀ n lambda, |lambda| < c →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      iteratedDeriv n F lambda =
        (n.factorial : ℝ) • F lambda ^ (n + 1)
  taylorNeumann :
    ∀ lambda h, |lambda| < c → |h| < c - |lambda| →
      let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj
      HasSum (fun n : ℕ => h ^ n • F lambda ^ (n + 1)) (F (lambda + h))
  analyticOnNhd :
    AnalyticOnNhd ℝ
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj)
      {lambda : ℝ | |lambda| < c}

/-- Construct the coherent support-resolvent analytic hierarchy package. -/
theorem realLinearPMapAmbientResolventAnalyticHierarchyPackage
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
    RealLinearPMapAmbientResolventAnalyticHierarchyPackage
      A c hc hNorm hKer hSurj := by
  refine ⟨?_, ?_, ?_⟩
  · intro n lambda hlambda
    exact realLinearPMapAmbientResolventFamily_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj n lambda hlambda
  · intro lambda h hlambda hh
    exact realLinearPMapAmbientResolventFamily_hasSum_taylorNeumann
      A c hc hNorm hKer hSurj lambda h hlambda hh
  · exact realLinearPMapAmbientResolventFamily_analyticOnNhd
      A c hc hNorm hKer hSurj

end

end MathlibAnalytic
end MGAP4D
