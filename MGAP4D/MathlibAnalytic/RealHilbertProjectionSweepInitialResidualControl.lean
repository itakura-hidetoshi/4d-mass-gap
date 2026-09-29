import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepSourceResidualProfile
import MGAP4D.MathlibAnalytic.RealRenewalTailContraction

/-!
# Initial residual control of an actual source profile

For a duplicate-free trajectory, each stage residual is bounded by its
original residual plus the SAME accumulated source forcing. Repetitions are
not silently removed. The scalar renewal lemma below keeps the zero-tail
hypothesis explicit and uses current-loss indexing.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The actual profile obeys the one-sided initial-residual comparison.
No self-adjointness, idempotence, or reordering is needed in this lemma. -/
theorem realHilbertProjectionSweepSourceResidualProfile_le_budget_add_initial
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype C] [DecidableEq C]
    (P : C → E →L[ℝ] E) (K : C → C → ℝ)
    (hK : ∀ source target, 0 ≤ K source target)
    (hStep : ∀ source target (x : E),
      ‖P source x - P target (P source x)‖ ≤
        ‖x - P target x‖ + K source target * ‖x - P source x‖)
    (sources : List C) (x : E) (hNodup : sources.Nodup) (target : C) :
    realHilbertProjectionSweepSourceResidualProfile P sources x target ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P
        (fun source y => K source target * ‖y - P source y‖) sources x + ‖x - P target x‖ := by
  have hBudget0 : ∀ (cs : List C) (y : E) (t : C),
      0 ≤ realHilbertProjectionSweepTargetResidualForcingBudget P
        (fun source z => K source t * ‖z - P source z‖) cs y := by
    intro cs y t
    rw [realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile]
    exact Finset.sum_nonneg fun source _ => mul_nonneg (hK source t)
      (realHilbertProjectionSweepSourceResidualProfile_nonneg P cs y source)
  induction sources generalizing x with
  | nil => simp [realHilbertProjectionSweepSourceResidualProfile,
      realHilbertProjectionSweepTargetResidualForcingBudget]
  | cons source sources ih =>
      by_cases hEq : target = source
      · subst target
        have hZero := realHilbertProjectionSweepSourceResidualProfile_eq_zero_of_notMem
          P sources (P source x) source hNodup.notMem
        change (if source = source then ‖x - P source x‖ else 0) +
          realHilbertProjectionSweepSourceResidualProfile P sources (P source x) source ≤ _
        rw [if_pos rfl, hZero, add_zero]
        exact le_add_of_nonneg_left (hBudget0 (source :: sources) x source)
      · have hTail := ih (P source x) hNodup.of_cons
        have hOne := hStep source target x
        change (if target = source then ‖x - P source x‖ else 0) +
            realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target ≤
          (K source target * ‖x - P source x‖ +
            realHilbertProjectionSweepTargetResidualForcingBudget P
              (fun next y => K next target * ‖y - P next y‖) sources (P source x)) + ‖x - P target x‖
        rw [if_neg hEq, zero_add]
        linarith

namespace RenewalTail

/-- Current-loss indexing: a proved zero tail and adjacent geometric loss
control imply a lower bound on the first loss. No rate for the tail is needed. -/
theorem current_loss_controls_energy_of_tendsto_zero
    (D L : ℕ → ℝ) (eta : ℝ)
    (hRenew : ∀ n, D n = L n + D (n + 1))
    (hLoss : ∀ n, L (n + 1) ≤ eta * L n)
    (hTail : Tendsto D atTop (𝓝 0)) : (1 - eta) * D 0 ≤ L 0 := by
  have hFinite : ∀ n : ℕ, D 1 - D (n + 1) ≤ eta * (D 0 - D n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          D 1 - D (n + 1 + 1) = (D 1 - D (n + 1)) + L (n + 1) := by
            linarith [hRenew (n + 1)]
          _ ≤ eta * (D 0 - D n) + eta * L n := _root_.add_le_add ih (hLoss n)
          _ = eta * (D 0 - D (n + 1)) := by rw [hRenew n]; ring
  have hShift : Tendsto (fun n : ℕ => D (n + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hTail
  have hLimit : Tendsto (fun n : ℕ => D (n + 1) - eta * D n) atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using hShift.sub (tendsto_const_nhds.mul hTail)
  have hBound : D 1 - eta * D 0 ≤ 0 :=
    ge_of_tendsto hLimit (Eventually.of_forall fun n => by nlinarith [hFinite n])
  nlinarith [hRenew 0]

end RenewalTail
end
end MGAP4D.MathlibAnalytic
