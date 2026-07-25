import MGAP4D.MathlibAnalytic.ContinuousLinearMapTwoSidedConfluentResolventJet
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coefficient of `Rlambda ^ (k + 1)` in the closed two-node confluent
normal form for multiplicities `m + 1` and `n + 1`. -/
noncomputable def twoSidedConfluentLeftBinomialCoefficient
    (q : ℝ) (m n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (m - k) *
    (Nat.choose (m - k + n) n : ℝ) *
      q ^ (m - k + n + 1)

/-- The coefficient of `Rmu ^ (k + 1)` in the closed two-node confluent normal
form for multiplicities `m + 1` and `n + 1`. -/
noncomputable def twoSidedConfluentRightBinomialCoefficient
    (q : ℝ) (m n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) *
    (Nat.choose (n - k + m) m : ℝ) *
      q ^ (n - k + m + 1)

/-- The left-node finite power sum in the closed two-node confluent normal
form. -/
noncomputable def twoSidedConfluentLeftBinomialSum
    (Rlambda : E →L[ℝ] E)
    (q : ℝ)
    (m n : ℕ) : E →L[ℝ] E :=
  (Finset.range (m + 1)).sum (fun k =>
    twoSidedConfluentLeftBinomialCoefficient q m n k •
      Rlambda ^ (k + 1))

/-- The right-node finite power sum in the closed two-node confluent normal
form. -/
noncomputable def twoSidedConfluentRightBinomialSum
    (Rmu : E →L[ℝ] E)
    (q : ℝ)
    (m n : ℕ) : E →L[ℝ] E :=
  (Finset.range (n + 1)).sum (fun k =>
    twoSidedConfluentRightBinomialCoefficient q m n k •
      Rmu ^ (k + 1))

/-- Closed binomial-coefficient normal form for two distinct resolvent nodes.
The parameters `m` and `n` encode the positive multiplicities `m + 1` and
`n + 1`. -/
noncomputable def twoSidedConfluentResolventBinomialNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (q : ℝ)
    (m n : ℕ) : E →L[ℝ] E :=
  twoSidedConfluentLeftBinomialSum Rlambda q m n +
    twoSidedConfluentRightBinomialSum Rmu q m n

private theorem leftCoefficient_succ_succ
    (q : ℝ) (m n k : ℕ) (hk : k ≤ m) :
    twoSidedConfluentLeftBinomialCoefficient q (m + 1) (n + 1) k =
      q *
        (twoSidedConfluentLeftBinomialCoefficient q (m + 1) n k -
          twoSidedConfluentLeftBinomialCoefficient q m (n + 1) k) := by
  have hmk : m + 1 - k = (m - k) + 1 := by omega
  have hTarget :
      twoSidedConfluentLeftBinomialCoefficient q (m + 1) (n + 1) k =
        (-1 : ℝ) ^ ((m - k) + 1) *
          (Nat.choose ((m - k) + n + 2) (n + 1) : ℝ) *
            q ^ ((m - k) + n + 3) := by
    simp only [twoSidedConfluentLeftBinomialCoefficient]
    rw [hmk]
    rw [show (m - k + 1) + (n + 1) = (m - k) + n + 2 by omega]
    rw [show (m - k) + n + 2 + 1 = (m - k) + n + 3 by omega]
  have hFirst :
      twoSidedConfluentLeftBinomialCoefficient q (m + 1) n k =
        (-1 : ℝ) ^ ((m - k) + 1) *
          (Nat.choose ((m - k) + n + 1) n : ℝ) *
            q ^ ((m - k) + n + 2) := by
    simp only [twoSidedConfluentLeftBinomialCoefficient]
    rw [hmk]
    rw [show (m - k + 1) + n = (m - k) + n + 1 by omega]
    rw [show (m - k) + n + 1 + 1 = (m - k) + n + 2 by omega]
  have hSecond :
      twoSidedConfluentLeftBinomialCoefficient q m (n + 1) k =
        (-1 : ℝ) ^ (m - k) *
          (Nat.choose ((m - k) + n + 1) (n + 1) : ℝ) *
            q ^ ((m - k) + n + 2) := by
    simp only [twoSidedConfluentLeftBinomialCoefficient]
    rw [show (m - k) + (n + 1) = (m - k) + n + 1 by omega]
    rw [show (m - k) + n + 1 + 1 = (m - k) + n + 2 by omega]
  rw [hTarget, hFirst, hSecond]
  have hChoose := Nat.choose_succ_succ' ((m - k) + n + 1) n
  have hCastChoose :
      (Nat.choose ((m - k) + n + 2) (n + 1) : ℝ) =
        (Nat.choose ((m - k) + n + 1) n : ℝ) +
          (Nat.choose ((m - k) + n + 1) (n + 1) : ℝ) := by
    exact_mod_cast hChoose
  rw [hCastChoose]
  have hSign :
      (-1 : ℝ) ^ ((m - k) + 1) =
        -((-1 : ℝ) ^ (m - k)) := by
    rw [pow_succ]
    ring
  have hPow :
      q ^ ((m - k) + n + 3) =
        q * q ^ ((m - k) + n + 2) := by
    rw [show (m - k) + n + 3 = ((m - k) + n + 2) + 1 by omega,
      pow_succ]
    ring
  rw [hSign, hPow]
  ring

private theorem leftCoefficient_top
    (q : ℝ) (m n : ℕ) :
    twoSidedConfluentLeftBinomialCoefficient q (m + 1) (n + 1) (m + 1) =
      q * twoSidedConfluentLeftBinomialCoefficient q (m + 1) n (m + 1) := by
  simp [twoSidedConfluentLeftBinomialCoefficient, pow_succ]
  ring

private theorem rightCoefficient_succ_succ
    (q : ℝ) (m n k : ℕ) (hk : k ≤ n) :
    twoSidedConfluentRightBinomialCoefficient q (m + 1) (n + 1) k =
      q *
        (twoSidedConfluentRightBinomialCoefficient q (m + 1) n k -
          twoSidedConfluentRightBinomialCoefficient q m (n + 1) k) := by
  have hnk : n + 1 - k = (n - k) + 1 := by omega
  have hTarget :
      twoSidedConfluentRightBinomialCoefficient q (m + 1) (n + 1) k =
        (-1 : ℝ) ^ (m + 2) *
          (Nat.choose ((n - k) + m + 2) (m + 1) : ℝ) *
            q ^ ((n - k) + m + 3) := by
    simp only [twoSidedConfluentRightBinomialCoefficient]
    rw [show m + 1 + 1 = m + 2 by omega, hnk]
    rw [show (n - k + 1) + (m + 1) = (n - k) + m + 2 by omega]
    rw [show (n - k) + m + 2 + 1 = (n - k) + m + 3 by omega]
  have hFirst :
      twoSidedConfluentRightBinomialCoefficient q (m + 1) n k =
        (-1 : ℝ) ^ (m + 2) *
          (Nat.choose ((n - k) + m + 1) (m + 1) : ℝ) *
            q ^ ((n - k) + m + 2) := by
    simp only [twoSidedConfluentRightBinomialCoefficient]
    rw [show m + 1 + 1 = m + 2 by omega]
    rw [show (n - k) + (m + 1) = (n - k) + m + 1 by omega]
    rw [show (n - k) + m + 1 + 1 = (n - k) + m + 2 by omega]
  have hSecond :
      twoSidedConfluentRightBinomialCoefficient q m (n + 1) k =
        (-1 : ℝ) ^ (m + 1) *
          (Nat.choose ((n - k) + m + 1) m : ℝ) *
            q ^ ((n - k) + m + 2) := by
    simp only [twoSidedConfluentRightBinomialCoefficient]
    rw [hnk]
    rw [show (n - k + 1) + m = (n - k) + m + 1 by omega]
    rw [show (n - k) + m + 1 + 1 = (n - k) + m + 2 by omega]
  rw [hTarget, hFirst, hSecond]
  have hChoose := Nat.choose_succ_succ' ((n - k) + m + 1) m
  have hCastChoose :
      (Nat.choose ((n - k) + m + 2) (m + 1) : ℝ) =
        (Nat.choose ((n - k) + m + 1) m : ℝ) +
          (Nat.choose ((n - k) + m + 1) (m + 1) : ℝ) := by
    exact_mod_cast hChoose
  rw [hCastChoose]
  have hSign :
      (-1 : ℝ) ^ (m + 2) = -((-1 : ℝ) ^ (m + 1)) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    ring
  have hPow :
      q ^ ((n - k) + m + 3) =
        q * q ^ ((n - k) + m + 2) := by
    rw [show (n - k) + m + 3 = ((n - k) + m + 2) + 1 by omega,
      pow_succ]
    ring
  rw [hSign, hPow]
  ring

private theorem rightCoefficient_top
    (q : ℝ) (m n : ℕ) :
    twoSidedConfluentRightBinomialCoefficient q (m + 1) (n + 1) (n + 1) =
      -q * twoSidedConfluentRightBinomialCoefficient q m (n + 1) (n + 1) := by
  simp [twoSidedConfluentRightBinomialCoefficient, pow_succ]
  ring

private theorem leftCoefficient_zero_succ
    (q : ℝ) (n : ℕ) :
    twoSidedConfluentLeftBinomialCoefficient q 0 (n + 1) 0 =
      q * twoSidedConfluentLeftBinomialCoefficient q 0 n 0 := by
  simp [twoSidedConfluentLeftBinomialCoefficient, pow_succ]
  ring

private theorem rightCoefficient_zero_succ
    (q : ℝ) (n k : ℕ) (hk : k ≤ n) :
    twoSidedConfluentRightBinomialCoefficient q 0 (n + 1) k =
      q * twoSidedConfluentRightBinomialCoefficient q 0 n k := by
  have hs : n + 1 - k = (n - k) + 1 := by omega
  simp [twoSidedConfluentRightBinomialCoefficient, hs, pow_succ]
  ring

private theorem rightCoefficient_zero_top
    (q : ℝ) (n : ℕ) :
    twoSidedConfluentRightBinomialCoefficient q 0 (n + 1) (n + 1) = -q := by
  simp [twoSidedConfluentRightBinomialCoefficient]

private theorem leftCoefficient_succ_zero
    (q : ℝ) (m k : ℕ) (hk : k ≤ m) :
    twoSidedConfluentLeftBinomialCoefficient q (m + 1) 0 k =
      -q * twoSidedConfluentLeftBinomialCoefficient q m 0 k := by
  have hs : m + 1 - k = (m - k) + 1 := by omega
  simp [twoSidedConfluentLeftBinomialCoefficient, hs, pow_succ]
  ring

private theorem leftCoefficient_succ_top
    (q : ℝ) (m : ℕ) :
    twoSidedConfluentLeftBinomialCoefficient q (m + 1) 0 (m + 1) = q := by
  simp [twoSidedConfluentLeftBinomialCoefficient]

private theorem rightCoefficient_succ_zero
    (q : ℝ) (m : ℕ) :
    twoSidedConfluentRightBinomialCoefficient q (m + 1) 0 0 =
      -q * twoSidedConfluentRightBinomialCoefficient q m 0 0 := by
  simp [twoSidedConfluentRightBinomialCoefficient, pow_succ]
  ring

private theorem leftBinomialSum_zero_succ
    (Rlambda : E →L[ℝ] E) (q : ℝ) (n : ℕ) :
    twoSidedConfluentLeftBinomialSum Rlambda q 0 (n + 1) =
      q • twoSidedConfluentLeftBinomialSum Rlambda q 0 n := by
  simp [twoSidedConfluentLeftBinomialSum, leftCoefficient_zero_succ,
    smul_smul]

private theorem rightBinomialSum_zero_succ
    (Rmu : E →L[ℝ] E) (q : ℝ) (n : ℕ) :
    twoSidedConfluentRightBinomialSum Rmu q 0 (n + 1) =
      q •
        (twoSidedConfluentRightBinomialSum Rmu q 0 n -
          Rmu ^ (n + 2)) := by
  have hPrefix :
      (Finset.range (n + 1)).sum (fun k =>
          twoSidedConfluentRightBinomialCoefficient q 0 (n + 1) k •
            Rmu ^ (k + 1)) =
        q •
          (Finset.range (n + 1)).sum (fun k =>
            twoSidedConfluentRightBinomialCoefficient q 0 n k •
              Rmu ^ (k + 1)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [rightCoefficient_zero_succ q n k hk', smul_smul]
  rw [twoSidedConfluentRightBinomialSum,
    twoSidedConfluentRightBinomialSum, Finset.sum_range_succ]
  rw [hPrefix, rightCoefficient_zero_top]
  simp [smul_sub]
  module

private theorem leftBinomialSum_succ_zero
    (Rlambda : E →L[ℝ] E) (q : ℝ) (m : ℕ) :
    twoSidedConfluentLeftBinomialSum Rlambda q (m + 1) 0 =
      q •
        (Rlambda ^ (m + 2) -
          twoSidedConfluentLeftBinomialSum Rlambda q m 0) := by
  have hPrefix :
      (Finset.range (m + 1)).sum (fun k =>
          twoSidedConfluentLeftBinomialCoefficient q (m + 1) 0 k •
            Rlambda ^ (k + 1)) =
        -q •
          (Finset.range (m + 1)).sum (fun k =>
            twoSidedConfluentLeftBinomialCoefficient q m 0 k •
              Rlambda ^ (k + 1)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [leftCoefficient_succ_zero q m k hk', smul_smul]
  rw [twoSidedConfluentLeftBinomialSum,
    twoSidedConfluentLeftBinomialSum, Finset.sum_range_succ]
  rw [hPrefix, leftCoefficient_succ_top]
  simp [smul_sub]
  module

private theorem rightBinomialSum_succ_zero
    (Rmu : E →L[ℝ] E) (q : ℝ) (m : ℕ) :
    twoSidedConfluentRightBinomialSum Rmu q (m + 1) 0 =
      -q • twoSidedConfluentRightBinomialSum Rmu q m 0 := by
  simp [twoSidedConfluentRightBinomialSum, rightCoefficient_succ_zero,
    smul_smul]

private theorem leftBinomialSum_succ_succ
    (Rlambda : E →L[ℝ] E) (q : ℝ) (m n : ℕ) :
    twoSidedConfluentLeftBinomialSum Rlambda q (m + 1) (n + 1) =
      q •
        (twoSidedConfluentLeftBinomialSum Rlambda q (m + 1) n -
          twoSidedConfluentLeftBinomialSum Rlambda q m (n + 1)) := by
  let targetPrefix :=
    (Finset.range (m + 1)).sum (fun k =>
      twoSidedConfluentLeftBinomialCoefficient q (m + 1) (n + 1) k •
        Rlambda ^ (k + 1))
  let firstPrefix :=
    (Finset.range (m + 1)).sum (fun k =>
      twoSidedConfluentLeftBinomialCoefficient q (m + 1) n k •
        Rlambda ^ (k + 1))
  let secondSum :=
    (Finset.range (m + 1)).sum (fun k =>
      twoSidedConfluentLeftBinomialCoefficient q m (n + 1) k •
        Rlambda ^ (k + 1))
  have hPrefix : targetPrefix = q • (firstPrefix - secondSum) := by
    dsimp [targetPrefix, firstPrefix, secondSum]
    rw [smul_sub, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [leftCoefficient_succ_succ q m n k hk', smul_smul, smul_smul]
    module
  have hTargetDecomp :
      twoSidedConfluentLeftBinomialSum Rlambda q (m + 1) (n + 1) =
        targetPrefix +
          twoSidedConfluentLeftBinomialCoefficient q (m + 1) (n + 1) (m + 1) •
            Rlambda ^ (m + 2) := by
    rw [twoSidedConfluentLeftBinomialSum, Finset.sum_range_succ]
    rfl
  have hFirstDecomp :
      twoSidedConfluentLeftBinomialSum Rlambda q (m + 1) n =
        firstPrefix +
          twoSidedConfluentLeftBinomialCoefficient q (m + 1) n (m + 1) •
            Rlambda ^ (m + 2) := by
    rw [twoSidedConfluentLeftBinomialSum, Finset.sum_range_succ]
    rfl
  have hSecond :
      twoSidedConfluentLeftBinomialSum Rlambda q m (n + 1) = secondSum := by
    rfl
  rw [hTargetDecomp, hPrefix, leftCoefficient_top, hFirstDecomp, hSecond,
    smul_smul]
  module

private theorem rightBinomialSum_succ_succ
    (Rmu : E →L[ℝ] E) (q : ℝ) (m n : ℕ) :
    twoSidedConfluentRightBinomialSum Rmu q (m + 1) (n + 1) =
      q •
        (twoSidedConfluentRightBinomialSum Rmu q (m + 1) n -
          twoSidedConfluentRightBinomialSum Rmu q m (n + 1)) := by
  let targetPrefix :=
    (Finset.range (n + 1)).sum (fun k =>
      twoSidedConfluentRightBinomialCoefficient q (m + 1) (n + 1) k •
        Rmu ^ (k + 1))
  let firstSum :=
    (Finset.range (n + 1)).sum (fun k =>
      twoSidedConfluentRightBinomialCoefficient q (m + 1) n k •
        Rmu ^ (k + 1))
  let secondPrefix :=
    (Finset.range (n + 1)).sum (fun k =>
      twoSidedConfluentRightBinomialCoefficient q m (n + 1) k •
        Rmu ^ (k + 1))
  have hPrefix : targetPrefix = q • (firstSum - secondPrefix) := by
    dsimp [targetPrefix, firstSum, secondPrefix]
    rw [smul_sub, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [rightCoefficient_succ_succ q m n k hk', smul_smul, smul_smul]
    module
  have hTargetDecomp :
      twoSidedConfluentRightBinomialSum Rmu q (m + 1) (n + 1) =
        targetPrefix +
          twoSidedConfluentRightBinomialCoefficient q (m + 1) (n + 1) (n + 1) •
            Rmu ^ (n + 2) := by
    rw [twoSidedConfluentRightBinomialSum, Finset.sum_range_succ]
    rfl
  have hSecondDecomp :
      twoSidedConfluentRightBinomialSum Rmu q m (n + 1) =
        secondPrefix +
          twoSidedConfluentRightBinomialCoefficient q m (n + 1) (n + 1) •
            Rmu ^ (n + 2) := by
    rw [twoSidedConfluentRightBinomialSum, Finset.sum_range_succ]
    rfl
  have hFirst :
      twoSidedConfluentRightBinomialSum Rmu q (m + 1) n = firstSum := by
    rfl
  rw [hTargetDecomp, hPrefix, rightCoefficient_top, hFirst, hSecondDecomp,
    smul_smul]
  module

@[simp] theorem twoSidedConfluentResolventBinomialNormalForm_zero_zero
    (Rlambda Rmu : E →L[ℝ] E)
    (q : ℝ) :
    twoSidedConfluentResolventBinomialNormalForm Rlambda Rmu q 0 0 =
      q • (Rlambda - Rmu) := by
  simp [twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentLeftBinomialSum,
    twoSidedConfluentRightBinomialSum,
    twoSidedConfluentLeftBinomialCoefficient,
    twoSidedConfluentRightBinomialCoefficient]
  module

private theorem binomialNormalForm_zero_succ
    (Rlambda Rmu : E →L[ℝ] E)
    (q : ℝ) (n : ℕ) :
    twoSidedConfluentResolventBinomialNormalForm Rlambda Rmu q 0 (n + 1) =
      q •
        (twoSidedConfluentResolventBinomialNormalForm Rlambda Rmu q 0 n -
          Rmu ^ (n + 2)) := by
  rw [twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentResolventBinomialNormalForm,
    leftBinomialSum_zero_succ, rightBinomialSum_zero_succ]
  module

private theorem binomialNormalForm_succ_zero
    (Rlambda Rmu : E →L[ℝ] E)
    (q : ℝ) (m : ℕ) :
    twoSidedConfluentResolventBinomialNormalForm Rlambda Rmu q (m + 1) 0 =
      q •
        (Rlambda ^ (m + 2) -
          twoSidedConfluentResolventBinomialNormalForm Rlambda Rmu q m 0) := by
  rw [twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentResolventBinomialNormalForm,
    leftBinomialSum_succ_zero, rightBinomialSum_succ_zero]
  module

private theorem binomialNormalForm_succ_succ
    (Rlambda Rmu : E →L[ℝ] E)
    (q : ℝ) (m n : ℕ) :
    twoSidedConfluentResolventBinomialNormalForm
        Rlambda Rmu q (m + 1) (n + 1) =
      q •
        (twoSidedConfluentResolventBinomialNormalForm
            Rlambda Rmu q (m + 1) n -
          twoSidedConfluentResolventBinomialNormalForm
            Rlambda Rmu q m (n + 1)) := by
  rw [twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentResolventBinomialNormalForm,
    leftBinomialSum_succ_succ, rightBinomialSum_succ_succ]
  module

/-- The recursively defined two-sided confluent jet is exactly the closed
binomial-coefficient normal form. -/
theorem twoSidedConfluentResolventJetNormalForm_succ_succ_eq_binomialNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ) :
    ∀ m n : ℕ,
      twoSidedConfluentResolventJetNormalForm
          Rlambda Rmu lambda mu (m + 1) (n + 1) =
        twoSidedConfluentResolventBinomialNormalForm
          Rlambda Rmu (lambda - mu)⁻¹ m n := by
  intro m
  induction m with
  | zero =>
      intro n
      induction n with
      | zero =>
          rw [twoSidedConfluentResolventJetNormalForm_succ_succ]
          simp
      | succ n ih =>
          rw [twoSidedConfluentResolventJetNormalForm_succ_succ]
          rw [ih]
          simp
          exact (binomialNormalForm_zero_succ
            Rlambda Rmu (lambda - mu)⁻¹ n).symm
  | succ m ihM =>
      intro n
      induction n with
      | zero =>
          rw [twoSidedConfluentResolventJetNormalForm_succ_succ]
          rw [ihM 0]
          simp
          exact (binomialNormalForm_succ_zero
            Rlambda Rmu (lambda - mu)⁻¹ m).symm
      | succ n ihN =>
          rw [twoSidedConfluentResolventJetNormalForm_succ_succ]
          rw [ihN, ihM (n + 1)]
          exact (binomialNormalForm_succ_succ
            Rlambda Rmu (lambda - mu)⁻¹ m n).symm

/-- Under the resolvent identity, arbitrary positive powers at two distinct
nodes have the closed finite binomial partial-fraction expansion. -/
theorem pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu))
    (m n : ℕ) :
    Rlambda ^ (m + 1) * Rmu ^ (n + 1) =
      twoSidedConfluentResolventBinomialNormalForm
        Rlambda Rmu (lambda - mu)⁻¹ m n := by
  rw [pow_mul_pow_eq_twoSidedConfluentResolventJetNormalForm
    Rlambda Rmu lambda mu hne hIdentity]
  exact
    twoSidedConfluentResolventJetNormalForm_succ_succ_eq_binomialNormalForm
      Rlambda Rmu lambda mu m n

/-- Pointwise closed binomial partial-fraction expansion. -/
theorem pow_succ_apply_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm_apply
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu))
    (m n : ℕ)
    (x : E) :
    (Rlambda ^ (m + 1)) ((Rmu ^ (n + 1)) x) =
      twoSidedConfluentResolventBinomialNormalForm
        Rlambda Rmu (lambda - mu)⁻¹ m n x := by
  have hOperator :=
    pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
      Rlambda Rmu lambda mu hne hIdentity m n
  exact DFunLike.congr_fun hOperator x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
