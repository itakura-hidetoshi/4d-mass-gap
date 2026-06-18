import MGAP4D.MathlibAnalytic.FinitePMFLikelihoodRatioTotalVariation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite partition function of real exponential weights. -/
def finiteExpPartition
    {X : Type*} [Fintype X]
    (logWeight : X → ℝ) : ℝ :=
  ∑ x : X, Real.exp (logWeight x)

/-- Normalized finite exponential weight, written directly in real arithmetic. -/
def finiteNormalizedExp
    {X : Type*} [Fintype X]
    (logWeight : X → ℝ) (x : X) : ℝ :=
  Real.exp (logWeight x) / finiteExpPartition logWeight

/-- A nonempty finite exponential partition function is strictly positive. -/
theorem finiteExpPartition_pos
    {X : Type*} [Fintype X] [Nonempty X]
    (logWeight : X → ℝ) :
    0 < finiteExpPartition logWeight := by
  classical
  let x : X := Classical.choice inferInstance
  unfold finiteExpPartition
  exact lt_of_lt_of_le (Real.exp_pos (logWeight x))
    (Finset.single_le_sum
      (fun y _hy => (Real.exp_pos (logWeight y)).le)
      (Finset.mem_univ x))

/-- Pointwise normalized exponential weights are nonnegative. -/
theorem finiteNormalizedExp_nonneg
    {X : Type*} [Fintype X] [Nonempty X]
    (logWeight : X → ℝ) (x : X) :
    0 ≤ finiteNormalizedExp logWeight x := by
  exact div_nonneg (Real.exp_pos _).le
    (finiteExpPartition_pos logWeight).le

/-- Oscillation control of the log-weight difference gives the sharp mutual
likelihood-ratio bound after normalization.

The hypothesis says that the difference `logWeight - referenceLogWeight` has
oscillation at most `R`.  Normalization does not cost a second factor: the
partition-function ratio is controlled by summing the same two-point
exponential comparison. -/
theorem finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
    {X : Type*} [Fintype X] [Nonempty X]
    (logWeight referenceLogWeight : X → ℝ)
    (R : ℝ)
    (hOsc : ∀ x y : X,
      (logWeight x - referenceLogWeight x) -
          (logWeight y - referenceLogWeight y) ≤ R)
    (x : X) :
    finiteNormalizedExp logWeight x ≤
        Real.exp R * finiteNormalizedExp referenceLogWeight x ∧
      finiteNormalizedExp referenceLogWeight x ≤
        Real.exp R * finiteNormalizedExp logWeight x := by
  classical
  have hZ : 0 < finiteExpPartition logWeight :=
    finiteExpPartition_pos logWeight
  have hZref : 0 < finiteExpPartition referenceLogWeight :=
    finiteExpPartition_pos referenceLogWeight
  constructor
  · unfold finiteNormalizedExp
    rw [show Real.exp R *
        (Real.exp (referenceLogWeight x) /
          finiteExpPartition referenceLogWeight) =
      (Real.exp R * Real.exp (referenceLogWeight x)) /
        finiteExpPartition referenceLogWeight by ring]
    apply (div_le_div_iff₀ hZ hZref).2
    unfold finiteExpPartition
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _hy
    calc
      Real.exp (logWeight x) * Real.exp (referenceLogWeight y) =
          Real.exp (logWeight x + referenceLogWeight y) := by
            rw [← Real.exp_add]
      _ ≤ Real.exp (R + referenceLogWeight x + logWeight y) := by
        apply Real.exp_le_exp.mpr
        linarith [hOsc x y]
      _ = Real.exp R * Real.exp (referenceLogWeight x) *
          Real.exp (logWeight y) := by
        rw [Real.exp_add, Real.exp_add]
  · unfold finiteNormalizedExp
    rw [show Real.exp R *
        (Real.exp (logWeight x) / finiteExpPartition logWeight) =
      (Real.exp R * Real.exp (logWeight x)) /
        finiteExpPartition logWeight by ring]
    apply (div_le_div_iff₀ hZref hZ).2
    unfold finiteExpPartition
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _hy
    calc
      Real.exp (referenceLogWeight x) * Real.exp (logWeight y) =
          Real.exp (referenceLogWeight x + logWeight y) := by
            rw [← Real.exp_add]
      _ ≤ Real.exp (R + logWeight x + referenceLogWeight y) := by
        apply Real.exp_le_exp.mpr
        linarith [hOsc y x]
      _ = Real.exp R * Real.exp (logWeight x) *
          Real.exp (referenceLogWeight y) := by
        rw [Real.exp_add, Real.exp_add]

/-- The same comparison packaged for all points. -/
theorem finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation_all
    {X : Type*} [Fintype X] [Nonempty X]
    (logWeight referenceLogWeight : X → ℝ)
    (R : ℝ)
    (hOsc : ∀ x y : X,
      (logWeight x - referenceLogWeight x) -
          (logWeight y - referenceLogWeight y) ≤ R) :
    ∀ x : X,
      finiteNormalizedExp logWeight x ≤
          Real.exp R * finiteNormalizedExp referenceLogWeight x ∧
        finiteNormalizedExp referenceLogWeight x ≤
          Real.exp R * finiteNormalizedExp logWeight x :=
  finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
    logWeight referenceLogWeight R hOsc

/-- An absolute two-sided bound on the log-weight difference gives an
oscillation bound with radius `2 * δ`. -/
theorem finiteNormalizedExp_mutual_le_exp_two_mul_of_abs_difference_le
    {X : Type*} [Fintype X] [Nonempty X]
    (logWeight referenceLogWeight : X → ℝ)
    (delta : ℝ)
    (hAbs : ∀ x : X,
      |logWeight x - referenceLogWeight x| ≤ delta) :
    ∀ x : X,
      finiteNormalizedExp logWeight x ≤
          Real.exp (2 * delta) * finiteNormalizedExp referenceLogWeight x ∧
        finiteNormalizedExp referenceLogWeight x ≤
          Real.exp (2 * delta) * finiteNormalizedExp logWeight x := by
  apply finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation_all
  intro x y
  have hx := (abs_le.mp (hAbs x)).2
  have hy := (abs_le.mp (hAbs y)).1
  linarith

end

end MathlibAnalytic
end MGAP4D
