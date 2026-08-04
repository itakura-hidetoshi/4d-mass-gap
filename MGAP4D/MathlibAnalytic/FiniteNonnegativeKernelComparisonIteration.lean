import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Action of a finite nonnegative comparison kernel on a real vector.
The orientation is `kernel target source`, matching the existing Dobrushin
influence matrices. -/
def finiteNonnegativeKernelApply
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (v : ι → ℝ)
    (target : ι) : ℝ :=
  ∑ source : ι, kernel target source * v source

/-- Iterated action of a finite comparison kernel. -/
def finiteNonnegativeKernelPowerApply
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (v : ι → ℝ)
    (n : ℕ) : ι → ℝ :=
  Nat.rec v
    (fun _ previous =>
      finiteNonnegativeKernelApply kernel previous)
    n

/-- Finite partial comparison resolvent.  The recursion is
`R_{n+1} b = b + C (R_n b)`. -/
def finiteNonnegativeKernelPartialResolvent
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (b : ι → ℝ)
    (n : ℕ) : ι → ℝ :=
  Nat.rec (fun _ => 0)
    (fun _ previous target =>
      b target + finiteNonnegativeKernelApply kernel previous target)
    n

/-- Scalar majorant for a finite partial comparison resolvent. -/
def finiteNonnegativeKernelScalarPartialResolvent
    (coefficient sourceBound : ℝ)
    (n : ℕ) : ℝ :=
  Nat.rec 0
    (fun _ previous => sourceBound + coefficient * previous)
    n

@[simp] theorem finiteNonnegativeKernelPowerApply_zero
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (v : ι → ℝ) :
    finiteNonnegativeKernelPowerApply kernel v 0 = v := by
  rfl

@[simp] theorem finiteNonnegativeKernelPowerApply_succ
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (v : ι → ℝ)
    (n : ℕ) :
    finiteNonnegativeKernelPowerApply kernel v (n + 1) =
      finiteNonnegativeKernelApply kernel
        (finiteNonnegativeKernelPowerApply kernel v n) := by
  rfl

@[simp] theorem finiteNonnegativeKernelPartialResolvent_zero
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (b : ι → ℝ) :
    finiteNonnegativeKernelPartialResolvent kernel b 0 = fun _ => 0 := by
  rfl

@[simp] theorem finiteNonnegativeKernelPartialResolvent_succ
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (b : ι → ℝ)
    (n : ℕ) :
    finiteNonnegativeKernelPartialResolvent kernel b (n + 1) =
      fun target =>
        b target +
          finiteNonnegativeKernelApply kernel
            (finiteNonnegativeKernelPartialResolvent kernel b n) target := by
  rfl

@[simp] theorem finiteNonnegativeKernelScalarPartialResolvent_zero
    (coefficient sourceBound : ℝ) :
    finiteNonnegativeKernelScalarPartialResolvent
      coefficient sourceBound 0 = 0 := by
  rfl

@[simp] theorem finiteNonnegativeKernelScalarPartialResolvent_succ
    (coefficient sourceBound : ℝ)
    (n : ℕ) :
    finiteNonnegativeKernelScalarPartialResolvent
        coefficient sourceBound (n + 1) =
      sourceBound + coefficient *
        finiteNonnegativeKernelScalarPartialResolvent
          coefficient sourceBound n := by
  rfl

/-- The finite kernel action is additive. -/
theorem finiteNonnegativeKernelApply_add
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (v w : ι → ℝ)
    (target : ι) :
    finiteNonnegativeKernelApply kernel (fun source => v source + w source) target =
      finiteNonnegativeKernelApply kernel v target +
        finiteNonnegativeKernelApply kernel w target := by
  unfold finiteNonnegativeKernelApply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _hsource
  ring

/-- The finite kernel action is homogeneous. -/
theorem finiteNonnegativeKernelApply_const_mul
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (a : ℝ)
    (v : ι → ℝ)
    (target : ι) :
    finiteNonnegativeKernelApply kernel (fun source => a * v source) target =
      a * finiteNonnegativeKernelApply kernel v target := by
  unfold finiteNonnegativeKernelApply
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _hsource
  ring

/-- A nonnegative finite kernel preserves pointwise order. -/
theorem finiteNonnegativeKernelApply_mono
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    {v w : ι → ℝ}
    (hvw : ∀ source : ι, v source ≤ w source)
    (target : ι) :
    finiteNonnegativeKernelApply kernel v target ≤
      finiteNonnegativeKernelApply kernel w target := by
  unfold finiteNonnegativeKernelApply
  apply Finset.sum_le_sum
  intro source _hsource
  exact mul_le_mul_of_nonneg_left (hvw source) (hKernel target source)

/-- A nonnegative finite kernel sends a nonnegative vector to a nonnegative
vector. -/
theorem finiteNonnegativeKernelApply_nonneg
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (v : ι → ℝ)
    (hv : ∀ source : ι, 0 ≤ v source)
    (target : ι) :
    0 ≤ finiteNonnegativeKernelApply kernel v target := by
  unfold finiteNonnegativeKernelApply
  exact Finset.sum_nonneg fun source _hsource =>
    mul_nonneg (hKernel target source) (hv source)

/-- Every power of a nonnegative finite kernel preserves pointwise order. -/
theorem finiteNonnegativeKernelPowerApply_mono
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    {v w : ι → ℝ}
    (hvw : ∀ source : ι, v source ≤ w source)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelPowerApply kernel v n target ≤
      finiteNonnegativeKernelPowerApply kernel w n target := by
  induction n generalizing target with
  | zero =>
      exact hvw target
  | succ n ih =>
      exact finiteNonnegativeKernelApply_mono
        kernel hKernel (fun source => ih source) target

/-- Every power of a nonnegative finite kernel preserves nonnegativity. -/
theorem finiteNonnegativeKernelPowerApply_nonneg
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (v : ι → ℝ)
    (hv : ∀ source : ι, 0 ≤ v source)
    (n : ℕ)
    (target : ι) :
    0 ≤ finiteNonnegativeKernelPowerApply kernel v n target := by
  induction n generalizing target with
  | zero =>
      exact hv target
  | succ n ih =>
      exact finiteNonnegativeKernelApply_nonneg
        kernel hKernel
        (finiteNonnegativeKernelPowerApply kernel v n)
        (fun source => ih source) target

/-- A partial comparison resolvent is nonnegative for a nonnegative kernel and
source vector. -/
theorem finiteNonnegativeKernelPartialResolvent_nonneg
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (b : ι → ℝ)
    (hb : ∀ target : ι, 0 ≤ b target)
    (n : ℕ)
    (target : ι) :
    0 ≤ finiteNonnegativeKernelPartialResolvent kernel b n target := by
  induction n generalizing target with
  | zero =>
      simp
  | succ n ih =>
      rw [finiteNonnegativeKernelPartialResolvent_succ]
      exact add_nonneg (hb target)
        (finiteNonnegativeKernelApply_nonneg
          kernel hKernel
          (finiteNonnegativeKernelPartialResolvent kernel b n)
          (fun source => ih source) target)

/-- Finite Dobrushin comparison iteration.  A pointwise inequality
`d ≤ b + C d` unfolds into a partial resolvent plus an explicit residual
`C^n d`. -/
theorem finiteNonnegativeKernelComparison_iterate
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (b d : ι → ℝ)
    (hComparison :
      ∀ target : ι,
        d target ≤ b target +
          finiteNonnegativeKernelApply kernel d target)
    (n : ℕ)
    (target : ι) :
    d target ≤
      finiteNonnegativeKernelPartialResolvent kernel b n target +
        finiteNonnegativeKernelPowerApply kernel d n target := by
  induction n generalizing target with
  | zero =>
      simp
  | succ n ih =>
      calc
        d target ≤ b target +
            finiteNonnegativeKernelApply kernel d target :=
          hComparison target
        _ ≤ b target +
            finiteNonnegativeKernelApply kernel
              (fun source =>
                finiteNonnegativeKernelPartialResolvent kernel b n source +
                  finiteNonnegativeKernelPowerApply kernel d n source)
              target := by
          exact add_le_add_left
            (finiteNonnegativeKernelApply_mono
              kernel hKernel (fun source => ih source) target)
            (b target)
        _ = finiteNonnegativeKernelPartialResolvent kernel b (n + 1) target +
            finiteNonnegativeKernelPowerApply kernel d (n + 1) target := by
          rw [finiteNonnegativeKernelApply_add,
            finiteNonnegativeKernelPartialResolvent_succ,
            finiteNonnegativeKernelPowerApply_succ]
          ring

/-- A row-sum coefficient bounds the action of a nonnegative comparison kernel
on every vector with a common pointwise upper bound. -/
theorem finiteNonnegativeKernelApply_le_coefficient_mul
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (coefficient : ℝ)
    (hRowSum :
      ∀ target : ι,
        ∑ source : ι, kernel target source ≤ coefficient)
    (v : ι → ℝ)
    (bound : ℝ)
    (hBound : 0 ≤ bound)
    (hv : ∀ source : ι, v source ≤ bound)
    (target : ι) :
    finiteNonnegativeKernelApply kernel v target ≤
      coefficient * bound := by
  calc
    finiteNonnegativeKernelApply kernel v target ≤
        ∑ source : ι, kernel target source * bound := by
      unfold finiteNonnegativeKernelApply
      apply Finset.sum_le_sum
      intro source _hsource
      exact mul_le_mul_of_nonneg_left (hv source)
        (hKernel target source)
    _ = (∑ source : ι, kernel target source) * bound := by
      rw [Finset.sum_mul]
    _ ≤ coefficient * bound :=
      mul_le_mul_of_nonneg_right (hRowSum target) hBound

/-- The row-sum coefficient controls every iterated residual. -/
theorem finiteNonnegativeKernelPowerApply_le_coefficient_pow_mul
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (coefficient : ℝ)
    (hCoefficient : 0 ≤ coefficient)
    (hRowSum :
      ∀ target : ι,
        ∑ source : ι, kernel target source ≤ coefficient)
    (v : ι → ℝ)
    (bound : ℝ)
    (hBound : 0 ≤ bound)
    (hv : ∀ source : ι, v source ≤ bound)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelPowerApply kernel v n target ≤
      coefficient ^ n * bound := by
  induction n generalizing target with
  | zero =>
      simpa using hv target
  | succ n ih =>
      calc
        finiteNonnegativeKernelPowerApply kernel v (n + 1) target =
            finiteNonnegativeKernelApply kernel
              (finiteNonnegativeKernelPowerApply kernel v n) target := by
          rfl
        _ ≤ coefficient * (coefficient ^ n * bound) :=
          finiteNonnegativeKernelApply_le_coefficient_mul
            kernel hKernel coefficient hRowSum
            (finiteNonnegativeKernelPowerApply kernel v n)
            (coefficient ^ n * bound)
            (mul_nonneg (pow_nonneg hCoefficient n) hBound)
            (fun source => ih source) target
        _ = coefficient ^ (n + 1) * bound := by
          rw [pow_succ]
          ring

/-- The scalar partial resolvent is nonnegative under nonnegative coefficient
and source bound. -/
theorem finiteNonnegativeKernelScalarPartialResolvent_nonneg
    (coefficient sourceBound : ℝ)
    (hCoefficient : 0 ≤ coefficient)
    (hSourceBound : 0 ≤ sourceBound)
    (n : ℕ) :
    0 ≤ finiteNonnegativeKernelScalarPartialResolvent
      coefficient sourceBound n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [finiteNonnegativeKernelScalarPartialResolvent_succ]
      exact add_nonneg hSourceBound (mul_nonneg hCoefficient ih)

/-- A row-sum coefficient and a uniform source bound majorize the finite
partial comparison resolvent. -/
theorem finiteNonnegativeKernelPartialResolvent_le_scalar
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (coefficient : ℝ)
    (hCoefficient : 0 ≤ coefficient)
    (hRowSum :
      ∀ target : ι,
        ∑ source : ι, kernel target source ≤ coefficient)
    (b : ι → ℝ)
    (sourceBound : ℝ)
    (hSourceBound : 0 ≤ sourceBound)
    (hb : ∀ target : ι, b target ≤ sourceBound)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelPartialResolvent kernel b n target ≤
      finiteNonnegativeKernelScalarPartialResolvent
        coefficient sourceBound n := by
  induction n generalizing target with
  | zero =>
      simp
  | succ n ih =>
      rw [finiteNonnegativeKernelPartialResolvent_succ,
        finiteNonnegativeKernelScalarPartialResolvent_succ]
      exact add_le_add (hb target)
        (finiteNonnegativeKernelApply_le_coefficient_mul
          kernel hKernel coefficient hRowSum
          (finiteNonnegativeKernelPartialResolvent kernel b n)
          (finiteNonnegativeKernelScalarPartialResolvent
            coefficient sourceBound n)
          (finiteNonnegativeKernelScalarPartialResolvent_nonneg
            coefficient sourceBound hCoefficient hSourceBound n)
          (fun source => ih source) target)

/-- Combined finite comparison estimate with an explicit geometric residual. -/
theorem finiteNonnegativeKernelComparison_iterate_le_scalar_add_residual
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hKernel : ∀ target source : ι, 0 ≤ kernel target source)
    (coefficient : ℝ)
    (hCoefficient : 0 ≤ coefficient)
    (hRowSum :
      ∀ target : ι,
        ∑ source : ι, kernel target source ≤ coefficient)
    (b d : ι → ℝ)
    (sourceBound distanceBound : ℝ)
    (hSourceBound : 0 ≤ sourceBound)
    (hDistanceBound : 0 ≤ distanceBound)
    (hb : ∀ target : ι, b target ≤ sourceBound)
    (hd : ∀ target : ι, d target ≤ distanceBound)
    (hComparison :
      ∀ target : ι,
        d target ≤ b target +
          finiteNonnegativeKernelApply kernel d target)
    (n : ℕ)
    (target : ι) :
    d target ≤
      finiteNonnegativeKernelScalarPartialResolvent
          coefficient sourceBound n +
        coefficient ^ n * distanceBound := by
  exact le_trans
    (finiteNonnegativeKernelComparison_iterate
      kernel hKernel b d hComparison n target)
    (add_le_add
      (finiteNonnegativeKernelPartialResolvent_le_scalar
        kernel hKernel coefficient hCoefficient hRowSum
        b sourceBound hSourceBound hb n target)
      (finiteNonnegativeKernelPowerApply_le_coefficient_pow_mul
        kernel hKernel coefficient hCoefficient hRowSum
        d distanceBound hDistanceBound hd n target))

end

end MathlibAnalytic
end MGAP4D