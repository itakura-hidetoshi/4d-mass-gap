import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDysonCore
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff LinearPMap Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The true real resolvent along the affine operator line `A + tH`. -/
def continuousLinearMapRealResolventOperatorLine
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z t : ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolvent (A + t • H) z

/-- Exact two-parameter identity along an affine operator line. -/
theorem continuousLinearMapRealResolventOperatorLine_sub_eq_smul_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ) {s t : ℝ}
    (hs : IsUnit (continuousLinearMapRealShift (A + s • H) z))
    (ht : IsUnit (continuousLinearMapRealShift (A + t • H) z)) :
    continuousLinearMapRealResolventOperatorLine A H z t -
        continuousLinearMapRealResolventOperatorLine A H z s =
      (t - s) •
        (continuousLinearMapRealResolventOperatorLine A H z t * H *
          continuousLinearMapRealResolventOperatorLine A H z s) := by
  unfold continuousLinearMapRealResolventOperatorLine
  rw [continuousLinearMapRealResolvent_sub_eq_mul_operator_sub_mul
    (A + s • H) (A + t • H) z hs ht]
  have hdiff : (A + t • H) - (A + s • H) = (t - s) • H := by
    module
  rw [hdiff]
  simp [mul_assoc]

/-- Uniform inverse bounds give a quantitative Lipschitz estimate along the
operator line. -/
theorem continuousLinearMapRealResolventOperatorLine_sub_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ) {s t M : ℝ}
    (hs : IsUnit (continuousLinearMapRealShift (A + s • H) z))
    (ht : IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hsNorm : ‖continuousLinearMapRealResolventOperatorLine A H z s‖ ≤ M)
    (htNorm : ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (hM : 0 ≤ M) :
    ‖continuousLinearMapRealResolventOperatorLine A H z t -
        continuousLinearMapRealResolventOperatorLine A H z s‖ ≤
      |t - s| * (M * ‖H‖ * M) := by
  rw [continuousLinearMapRealResolventOperatorLine_sub_eq_smul_mul A H z hs ht,
    norm_smul, Real.norm_eq_abs]
  calc
    |t - s| *
        ‖continuousLinearMapRealResolventOperatorLine A H z t * H *
          continuousLinearMapRealResolventOperatorLine A H z s‖ ≤
      |t - s| *
        ((‖continuousLinearMapRealResolventOperatorLine A H z t‖ * ‖H‖) *
          ‖continuousLinearMapRealResolventOperatorLine A H z s‖) := by
      gcongr
      exact norm_mul_le _ _ |>.trans <|
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ |t - s| * (M * ‖H‖ * M) := by gcongr

/-- Uniformly bounded resolvents are Lipschitz along an affine operator line. -/
theorem continuousLinearMapRealResolventOperatorLine_lipschitzOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (M * ‖H‖ * M))
      (continuousLinearMapRealResolventOperatorLine A H z) U := by
  apply LipschitzOnWith.of_dist_le'
  intro s hs t ht
  rw [dist_eq_norm]
  have hbound := continuousLinearMapRealResolventOperatorLine_sub_norm_le
    A H z (hunit s hs) (hunit t ht) (hnorm s hs) (hnorm t ht) hM
  calc
    ‖continuousLinearMapRealResolventOperatorLine A H z s -
        continuousLinearMapRealResolventOperatorLine A H z t‖ =
      ‖continuousLinearMapRealResolventOperatorLine A H z t -
        continuousLinearMapRealResolventOperatorLine A H z s‖ := by
      rw [norm_sub_rev]
    _ ≤ |t - s| * (M * ‖H‖ * M) := hbound
    _ = (M * ‖H‖ * M) * dist s t := by
      rw [Real.dist_eq]
      rw [abs_sub_comm]
      ring

/-- Uniformly bounded resolvents depend continuously on the operator-line
parameter. -/
theorem continuousLinearMapRealResolventOperatorLine_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M) :
    ContinuousOn (continuousLinearMapRealResolventOperatorLine A H z) U :=
  (continuousLinearMapRealResolventOperatorLine_lipschitzOn
    A H z U M hM hunit hnorm).continuousOn

/-- The operator-direction derivative of a true real resolvent is `R H R`. -/
theorem continuousLinearMapRealResolventOperatorLine_hasDerivWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivWithinAt
      (continuousLinearMapRealResolventOperatorLine A H z)
      (continuousLinearMapRealResolventOperatorLine A H z t * H *
        continuousLinearMapRealResolventOperatorLine A H z t) U t := by
  refine (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ)
    (f := continuousLinearMapRealResolventOperatorLine A H z)
    (f' := continuousLinearMapRealResolventOperatorLine A H z t * H *
      continuousLinearMapRealResolventOperatorLine A H z t)
    (s := U) (x := t)).2 ?_
  let Rt := continuousLinearMapRealResolventOperatorLine A H z t
  have hres0 : Tendsto (continuousLinearMapRealResolventOperatorLine A H z)
      (𝓝[U] t) (𝓝 (continuousLinearMapRealResolventOperatorLine A H z t)) :=
    continuousLinearMapRealResolventOperatorLine_continuousOn
      A H z U M hM hunit hnorm t ht
  have hres : Tendsto (continuousLinearMapRealResolventOperatorLine A H z)
      (𝓝[U] t) (𝓝 Rt) := by simpa [Rt] using hres0
  have hres' : Tendsto (continuousLinearMapRealResolventOperatorLine A H z)
      (𝓝[U \ {t}] t) (𝓝 Rt) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro w hw
      exact hw.1
  have hmul : Tendsto
      (fun w => continuousLinearMapRealResolventOperatorLine A H z w * H * Rt)
      (𝓝[U \ {t}] t) (𝓝 (Rt * H * Rt)) :=
    (hres'.mul tendsto_const_nhds).mul tendsto_const_nhds
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rcases hw with ⟨hwU, hwNe⟩
  have hne : w - t ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hwNe
  rw [slope_def_module,
    continuousLinearMapRealResolventOperatorLine_sub_eq_smul_mul
      A H z (hunit t ht) (hunit w hwU)]
  rw [inv_smul_smul₀ hne]

/-- On an open operator-line resolvent region the within derivative is the
ordinary derivative. -/
theorem continuousLinearMapRealResolventOperatorLine_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt
      (continuousLinearMapRealResolventOperatorLine A H z)
      (continuousLinearMapRealResolventOperatorLine A H z t * H *
        continuousLinearMapRealResolventOperatorLine A H z t) t :=
  (continuousLinearMapRealResolventOperatorLine_hasDerivWithinAt
    A H z U M hM hunit hnorm ht).hasDerivAt (hU.mem_nhds ht)

/-- Explicit ordinary operator-direction derivative formula. -/
theorem continuousLinearMapRealResolventOperatorLine_deriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    {t : ℝ} (ht : t ∈ U) :
    deriv (continuousLinearMapRealResolventOperatorLine A H z) t =
      continuousLinearMapRealResolventOperatorLine A H z t * H *
        continuousLinearMapRealResolventOperatorLine A H z t :=
  (continuousLinearMapRealResolventOperatorLine_hasDerivAt
    A H z U M hU hM hunit hnorm ht).deriv

/-- Dyson coefficients satisfy the recursion `C_(n+1) = C_n H R`. -/
@[simp]
theorem continuousLinearMapRealResolventOperatorDysonCoefficient_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1) A H z =
      continuousLinearMapRealResolventOperatorDysonCoefficient n A H z * H *
        continuousLinearMapRealResolvent A z := by
  unfold continuousLinearMapRealResolventOperatorDysonCoefficient
  rw [pow_succ]
  noncomm_ring

@[simp]
theorem continuousLinearMapRealResolventOperatorDysonCoefficient_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorDysonCoefficient 0 A H z =
      continuousLinearMapRealResolvent A z := by
  simp [continuousLinearMapRealResolventOperatorDysonCoefficient]

/-- The derivative of the `n`-th Dyson coefficient is `(n+1) C_(n+1)`. -/
theorem continuousLinearMapRealResolventOperatorDysonCoefficient_hasDerivWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    HasDerivWithinAt
      (fun s => continuousLinearMapRealResolventOperatorDysonCoefficient n
        (A + s • H) H z)
      (((n + 1 : ℕ) : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1)
          (A + t • H) H z) U t := by
  induction n with
  | zero =>
      simpa using continuousLinearMapRealResolventOperatorLine_hasDerivWithinAt
        A H z U M hM hunit hnorm ht
  | succ n ih =>
      have hconst : HasDerivWithinAt (fun _ : ℝ => H) 0 U t :=
        hasDerivWithinAt_const t U H
      have hR := continuousLinearMapRealResolventOperatorLine_hasDerivWithinAt
        A H z U M hM hunit hnorm ht
      have hmulH := HasDerivWithinAt.mul
        (𝕜 := ℝ) (𝔸 := V →L[ℝ] V) ih hconst
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ) (𝔸 := V →L[ℝ] V) hmulH hR
      have hraw : HasDerivWithinAt
          (fun s => continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1)
            (A + s • H) H z)
          (((((n + 1 : ℕ) : ℝ) •
              continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1)
                (A + t • H) H z) * H) *
              continuousLinearMapRealResolventOperatorLine A H z t +
            (continuousLinearMapRealResolventOperatorDysonCoefficient n
              (A + t • H) H z * H) *
              (continuousLinearMapRealResolventOperatorLine A H z t * H *
                continuousLinearMapRealResolventOperatorLine A H z t)) U t := by
        simpa [continuousLinearMapRealResolventOperatorLine] using hmul
      have hderiv :
          (((((n + 1 : ℕ) : ℝ) •
              continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1)
                (A + t • H) H z) * H) *
              continuousLinearMapRealResolventOperatorLine A H z t +
            (continuousLinearMapRealResolventOperatorDysonCoefficient n
              (A + t • H) H z * H) *
              (continuousLinearMapRealResolventOperatorLine A H z t * H *
                continuousLinearMapRealResolventOperatorLine A H z t)) =
          (((Nat.succ n + 1 : ℕ) : ℝ) •
            continuousLinearMapRealResolventOperatorDysonCoefficient
              (Nat.succ n + 1) (A + t • H) H z) := by
        let Rt := continuousLinearMapRealResolventOperatorLine A H z t
        let P := Rt * H
        change
          (((((n + 1 : ℕ) : ℝ) • (P ^ (n + 1) * Rt)) * H) * Rt +
            (P ^ n * Rt * H) * (Rt * H * Rt)) =
          (((n + 2 : ℕ) : ℝ) • (P ^ (n + 2) * Rt))
        have hfirst :
            (P ^ (n + 1) * Rt) * H * Rt = P ^ (n + 2) * Rt := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          simp [P, mul_assoc]
        have hpow : P ^ (n + 2) * Rt = ((P ^ n * P) * P) * Rt := by
          calc
            P ^ (n + 2) * Rt = (P ^ (n + 1) * P) * Rt := by
              rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
            _ = ((P ^ n * P) * P) * Rt := by rw [pow_succ]
        have hsecond :
            (P ^ n * Rt * H) * (Rt * H * Rt) = P ^ (n + 2) * Rt := by
          calc
            (P ^ n * Rt * H) * (Rt * H * Rt) =
                (P ^ n * P) * (P * Rt) := by
              simp only [P]
              simp [mul_assoc]
            _ = ((P ^ n * P) * P) * Rt := by rw [mul_assoc]
            _ = P ^ (n + 2) * Rt := hpow.symm
        have hsmul :
            (((((n + 1 : ℕ) : ℝ) • (P ^ (n + 1) * Rt)) * H) * Rt) =
              (((n + 1 : ℕ) : ℝ) • (P ^ (n + 2) * Rt)) := by
          rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, hfirst]
        rw [hsmul, hsecond]
        have hcast : (((n + 2 : ℕ) : ℝ)) = (((n + 1 : ℕ) : ℝ)) + 1 := by
          push_cast
          ring
        rw [hcast]
        module
      rw [hderiv] at hraw
      exact hraw

/-- Every iterated operator-direction derivative is the factorial multiple of
the corresponding Dyson coefficient. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDerivWithin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    iteratedDerivWithin n
        (continuousLinearMapRealResolventOperatorLine A H z) U t =
      (n.factorial : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient n
          (A + t • H) H z := by
  induction n generalizing t with
  | zero => simp [continuousLinearMapRealResolventOperatorLine]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (continuousLinearMapRealResolventOperatorLine A H z) U) U t =
            derivWithin
              (fun s => (n.factorial : ℝ) •
                continuousLinearMapRealResolventOperatorDysonCoefficient n
                  (A + s • H) H z) U t :=
        derivWithin_congr
          (fun s hs => ih (t := s) hs)
          (ih (t := t) ht)
      rw [hcongr]
      have hcoeff :=
        continuousLinearMapRealResolventOperatorDysonCoefficient_hasDerivWithinAt
          A H z U M hM hunit hnorm n ht
      have hscaled : HasDerivWithinAt
          (fun s => (n.factorial : ℝ) •
            continuousLinearMapRealResolventOperatorDysonCoefficient n
              (A + s • H) H z)
          ((n.factorial : ℝ) •
            ((((n + 1 : ℕ) : ℝ) •
              continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1)
                (A + t • H) H z))) U t := by
        simpa only [Pi.smul_apply] using
          (HasDerivWithinAt.const_smul
            (𝕜 := ℝ) (R := ℝ) (F := V →L[ℝ] V)
            (n.factorial : ℝ) hcoeff)
      let derivativeValue : V →L[ℝ] V :=
        (n.factorial : ℝ) •
          ((((n + 1 : ℕ) : ℝ) •
            continuousLinearMapRealResolventOperatorDysonCoefficient (n + 1)
              (A + t • H) H z))
      have hfscaled : HasFDerivWithinAt
          (fun s => (n.factorial : ℝ) •
            continuousLinearMapRealResolventOperatorDysonCoefficient n
              (A + s • H) H z)
          (toSpanSingleton ℝ derivativeValue) U t := by
        simpa [derivativeValue] using hscaled.hasFDerivWithinAt
      have hfderiv : fderivWithin ℝ
          (fun s => (n.factorial : ℝ) •
            continuousLinearMapRealResolventOperatorDysonCoefficient n
              (A + s • H) H z) U t =
          toSpanSingleton ℝ derivativeValue :=
        hfscaled.fderivWithin (hU.uniqueDiffOn t ht)
      have hscaledDeriv : derivWithin
          (fun s => (n.factorial : ℝ) •
            continuousLinearMapRealResolventOperatorDysonCoefficient n
              (A + s • H) H z) U t = derivativeValue := by
        unfold derivWithin
        rw [hfderiv]
        simp [derivativeValue]
      rw [hscaledDeriv]
      simp only [derivativeValue, smul_smul, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_succ]
      congr 1
      ring

/-- Explicit ordinary all-order operator-direction derivative formula. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t =
      (n.factorial : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient n
          (A + t • H) H z := by
  calc
    iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t =
      iteratedDerivWithin n
        (continuousLinearMapRealResolventOperatorLine A H z) U t :=
      (iteratedDerivWithin_of_isOpen
        (n := n) (f := continuousLinearMapRealResolventOperatorLine A H z)
        hU ht).symm
    _ = (n.factorial : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient n
          (A + t • H) H z :=
      continuousLinearMapRealResolventOperatorLine_iteratedDerivWithin
        A H z U M hU hM hunit hnorm n ht

/-- Factorial Cauchy-type bound for all operator-direction derivatives. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDeriv_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    ‖iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t‖ ≤
      (n.factorial : ℝ) * (M * ‖H‖) ^ n * M := by
  rw [continuousLinearMapRealResolventOperatorLine_iteratedDeriv
    A H z U M hU hM hunit hnorm n ht]
  let Rt := continuousLinearMapRealResolventOperatorLine A H z t
  let P := Rt * H
  change ‖(n.factorial : ℝ) • (P ^ n * Rt)‖ ≤
    (n.factorial : ℝ) * (M * ‖H‖) ^ n * M
  calc
    ‖(n.factorial : ℝ) • (P ^ n * Rt)‖ ≤
        ‖(n.factorial : ℝ)‖ * ‖P ^ n * Rt‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = (n.factorial : ℝ) * ‖P ^ n * Rt‖ := by simp
    _ ≤ (n.factorial : ℝ) * (‖P ^ n‖ * ‖Rt‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ (n.factorial : ℝ) * (‖P‖ ^ n * ‖Rt‖) := by
      gcongr
      induction n with
      | zero =>
          simp only [pow_zero]
          apply ContinuousLinearMap.opNorm_le_bound
          · norm_num
          intro x
          simp
      | succ k ih =>
          rw [pow_succ]
          calc
            ‖P ^ k * P‖ ≤ ‖P ^ k‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ ‖P‖ ^ k * ‖P‖ :=
              mul_le_mul_of_nonneg_right ih (norm_nonneg P)
            _ = ‖P‖ ^ (k + 1) := by rw [pow_succ]
    _ ≤ (n.factorial : ℝ) * ((M * ‖H‖) ^ n * M) := by
      gcongr
      · calc
          ‖P‖ ≤ ‖Rt‖ * ‖H‖ := norm_mul_le _ _
          _ ≤ M * ‖H‖ := mul_le_mul_of_nonneg_right (hnorm t ht) (norm_nonneg H)
      · exact hnorm t ht
    _ = (n.factorial : ℝ) * (M * ‖H‖) ^ n * M := by ring

/-- The finite all-order operator-direction derivative jet. -/
def continuousLinearMapRealResolventOperatorDirectionalJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z t : ℝ) :
    Fin N → (V →L[ℝ] V) :=
  fun n => (n.1.factorial : ℝ) •
    continuousLinearMapRealResolventOperatorDysonCoefficient n.1
      (A + t • H) H z

end MathlibAnalytic
end MGAP4D
