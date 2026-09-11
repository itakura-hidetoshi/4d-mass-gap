import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchy
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The right affine inverse is real analytic at every unit shift. -/
theorem ringInverse_smul_one_sub_analyticAt
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda : ℝ)
    (hunit : IsUnit (lambda • (1 : R) - G)) :
    AnalyticAt ℝ
      (fun mu : ℝ => Ring.inverse (mu • (1 : R) - G))
      lambda := by
  have hid : AnalyticAt ℝ (fun mu : ℝ => mu) lambda := analyticAt_id
  have hone : AnalyticAt ℝ (fun _ : ℝ => (1 : R)) lambda := analyticAt_const
  have hG : AnalyticAt ℝ (fun _ : ℝ => G) lambda := analyticAt_const
  have hsmul : AnalyticAt ℝ (fun mu : ℝ => mu • (1 : R)) lambda :=
    hid.smul hone
  have hshift : AnalyticAt ℝ (fun mu : ℝ => mu • (1 : R) - G) lambda :=
    hsmul.sub hG
  have hinverse : AnalyticAt ℝ Ring.inverse (lambda • (1 : R) - G) := by
    simpa only [hunit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℝ) hunit.unit)
  exact AnalyticAt.comp'
    (𝕜 := ℝ)
    (g := fun x : R => Ring.inverse x)
    (f := fun mu : ℝ => mu • (1 : R) - G)
    hinverse hshift

/-- If `S' = -S²` on a right half-line, then `(S^k)' = -k S^(k+1)` there. -/
theorem rightResolvent_pow_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (k : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda) :
    HasDerivWithinAt
      (fun mu => res mu ^ k)
      (-((k : ℝ) • res lambda ^ (k + 1)))
      (Set.Ioi edge)
      lambda := by
  induction k with
  | zero =>
      simpa using (hasDerivWithinAt_const lambda (Set.Ioi edge) (1 : A))
  | succ k ih =>
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ) (𝔸 := A) ih (hres hlambda)
      have hmul' :
          HasDerivWithinAt
            (fun mu => res mu ^ (k + 1))
            ((-((k : ℝ) • res lambda ^ (k + 1))) * res lambda +
              res lambda ^ k * (-(res lambda ^ 2)))
            (Set.Ioi edge) lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((-((k : ℝ) • res lambda ^ (k + 1))) * res lambda +
              res lambda ^ k * (-(res lambda ^ 2))) =
            -(((Nat.succ k : ℕ) : ℝ) •
              res lambda ^ (Nat.succ k + 1)) := by
        let x := res lambda
        change
          (-((k : ℝ) • x ^ (k + 1))) * x + x ^ k * (-(x ^ 2)) =
            -(((Nat.succ k : ℕ) : ℝ) • x ^ (Nat.succ k + 1))
        have hfirst :
            ((k : ℝ) • x ^ (k + 1)) * x =
              (k : ℝ) • x ^ (k + 2) := by
          rw [Algebra.smul_mul_assoc]
          congr 1
          simpa [Nat.add_assoc] using (pow_succ x (k + 1)).symm
        have hsecond : x ^ k * x ^ 2 = x ^ (k + 2) := by
          simpa using (pow_add x k 2).symm
        rw [neg_mul, hfirst, mul_neg, hsecond,
          show Nat.succ k + 1 = k + 2 by omega, Nat.cast_succ]
        module
      rw [hderiv] at hmul'
      exact hmul'

/-- Unsigned factorial powers gain one minus sign under differentiation on a
right resolvent half-line. -/
theorem rightResolvent_factorialDerivativeStep_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda) :
    HasDerivWithinAt
      (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
      (-(((n + 1).factorial : ℝ) • res lambda ^ (n + 2)))
      (Set.Ioi edge) lambda := by
  have hpow :=
    rightResolvent_pow_hasDerivWithinAt res edge hres (n + 1) hlambda
  have hscaled :
      HasDerivWithinAt
        (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
        ((n.factorial : ℝ) •
          (-(((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2))))
        (Set.Ioi edge) lambda := by
    simpa only [Pi.smul_apply] using
      (HasDerivWithinAt.const_smul
        (𝕜 := ℝ) (R := ℝ) (F := A)
        (n.factorial : ℝ) hpow)
  simpa [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    smul_smul, mul_comm, Nat.add_assoc] using hscaled

/-- The sign-weighted factorial operator candidate differentiates to the next
sign-weighted factorial candidate. -/
theorem rightResolvent_alternatingFactorialDerivativeStep_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda) :
    HasDerivWithinAt
      (((-1 : ℝ) ^ n) •
        (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1)))
      (((-1 : ℝ) ^ (n + 1)) •
        (((n + 1).factorial : ℝ) • res lambda ^ (n + 2)))
      (Set.Ioi edge) lambda := by
  have hbase :=
    rightResolvent_factorialDerivativeStep_hasDerivWithinAt
      res edge hres n hlambda
  have hsigned :=
    HasDerivWithinAt.const_smul
      (𝕜 := ℝ) (R := ℝ) (F := A)
      ((-1 : ℝ) ^ n) hbase
  simpa [pow_succ, smul_smul] using hsigned

/-- Fixed-vector quadratic evaluation of the sign-weighted factorial operator
candidate satisfies the same recurrence. -/
theorem rightResolvent_quadratic_alternatingFactorialDerivativeStep_hasDerivWithinAt
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda)
    (u : E) :
    HasDerivWithinAt
      (fun mu : ℝ =>
        ((-1 : ℝ) ^ n) *
          ((n.factorial : ℝ) * inner ℝ ((res mu ^ (n + 1)) u) u))
      (((-1 : ℝ) ^ (n + 1)) *
        (((n + 1).factorial : ℝ) *
          inner ℝ ((res lambda ^ (n + 2)) u) u))
      (Set.Ioi edge) lambda := by
  have hop :=
    rightResolvent_alternatingFactorialDerivativeStep_hasDerivWithinAt
      res edge hres n hlambda
  have hquad := HasDerivWithinAt.quadraticEvaluation hop u
  simpa only [Pi.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, smul_eq_mul, mul_assoc] using hquad

/-- Exact all-order scalar formula on an abstract right resolvent half-line. -/
theorem rightResolvent_quadratic_iteratedDerivWithin_eq_alternating_factorial
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda)
    (u : E) :
    iteratedDerivWithin n
        (fun mu : ℝ => inner ℝ (res mu u) u)
        (Set.Ioi edge) lambda =
      ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (fun mu : ℝ => inner ℝ (res mu u) u)
                (Set.Ioi edge))
              (Set.Ioi edge) lambda =
            derivWithin
              (fun mu : ℝ =>
                ((-1 : ℝ) ^ n) *
                  ((n.factorial : ℝ) *
                    inner ℝ ((res mu ^ (n + 1)) u) u))
              (Set.Ioi edge) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hstep :=
        rightResolvent_quadratic_alternatingFactorialDerivativeStep_hasDerivWithinAt
          res edge hres n hlambda u
      exact hstep.derivWithin (isOpen_Ioi.uniqueDiffOn lambda hlambda)

/-- Ordinary exact all-order scalar formula at interior points. -/
theorem rightResolvent_quadratic_iteratedDeriv_eq_alternating_factorial
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda)
    (u : E) :
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
      ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u) := by
  calc
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
        iteratedDerivWithin n
          (fun mu : ℝ => inner ℝ (res mu u) u)
          (Set.Ioi edge) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := fun mu : ℝ => inner ℝ (res mu u) u)
        isOpen_Ioi hlambda).symm
    _ = ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u) :=
      rightResolvent_quadratic_iteratedDerivWithin_eq_alternating_factorial
        res edge hres n hlambda u

/-- Alternating sign does not enlarge the factorial power norm estimate. -/
theorem continuousLinearMap_alternating_factorial_smul_pow_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (n : ℕ)
    (M : ℝ)
    (hA : ‖A‖ ≤ M) :
    ‖((-1 : ℝ) ^ n) • ((n.factorial : ℝ) • A ^ (n + 1))‖ ≤
      (n.factorial : ℝ) * M ^ (n + 1) := by
  rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact continuousLinearMap_factorial_smul_pow_norm_le A n M hA

end

end MathlibAnalytic
end MGAP4D
