import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Renewal contraction with the tail kept explicit

Geometric loss decay does not by itself eliminate a persistent defect tail.
The finite comparison retains both tails. Its limit controls the defect above
the limiting tail; the zero-tail specialization is a separate theorem.
-/

namespace MGAP4D.MathlibAnalytic.RenewalTail

open Filter
open scoped Topology

/-- Exact finite-tail comparison, without hidden positivity or convergence. -/
theorem defect_sub_tail_le_mul (D L : ℕ → ℝ) (eta : ℝ)
    (hRenew : ∀ n, D n = L (n + 1) + D (n + 1))
    (hLoss : ∀ n, L (n + 2) ≤ eta * L (n + 1)) (n : ℕ) :
    D 1 - D (n + 1) ≤ eta * (D 0 - D n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        D 1 - D (n + 1 + 1) = (D 1 - D (n + 1)) + L (n + 2) := by
          linarith [hRenew (n + 1)]
        _ ≤ eta * (D 0 - D n) + eta * L (n + 1) :=
          _root_.add_le_add ih (hLoss n)
        _ = eta * (D 0 - D (n + 1)) := by
          rw [hRenew n]
          ring

/-- A nonzero limiting tail is subtracted, not silently discarded. -/
theorem defect_succ_sub_limit_le_mul (D L : ℕ → ℝ) (eta tail : ℝ)
    (hRenew : ∀ n, D n = L (n + 1) + D (n + 1))
    (hLoss : ∀ n, L (n + 2) ≤ eta * L (n + 1))
    (hTail : Tendsto D atTop (𝓝 tail)) :
    D 1 - tail ≤ eta * (D 0 - tail) := by
  have hShift : Tendsto (fun n : ℕ => D (n + 1)) atTop (𝓝 tail) :=
    (tendsto_add_atTop_iff_nat 1).2 hTail
  have hLimit : Tendsto (fun n : ℕ => D (n + 1) - eta * D n)
      atTop (𝓝 (tail - eta * tail)) :=
    hShift.sub (tendsto_const_nhds.mul hTail)
  have hBound : D 1 - eta * D 0 ≤ tail - eta * tail :=
    ge_of_tendsto hLimit (Eventually.of_forall (fun n => by
      have h := defect_sub_tail_le_mul D L eta hRenew hLoss n
      nlinarith))
  nlinarith

/-- Loss decay yields actual defect contraction once the tail is proved zero. -/
theorem defect_succ_le_mul_of_tendsto_zero (D L : ℕ → ℝ) (eta : ℝ)
    (hRenew : ∀ n, D n = L (n + 1) + D (n + 1))
    (hLoss : ∀ n, L (n + 2) ≤ eta * L (n + 1))
    (hTail : Tendsto D atTop (𝓝 0)) : D 1 ≤ eta * D 0 := by
  simpa only [sub_zero] using
    defect_succ_sub_limit_le_mul D L eta 0 hRenew hLoss hTail

end MGAP4D.MathlibAnalytic.RenewalTail
