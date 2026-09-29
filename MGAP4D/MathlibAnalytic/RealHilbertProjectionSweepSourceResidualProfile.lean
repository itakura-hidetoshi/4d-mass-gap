import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetProfileSum

/-!
# Exact source-residual profile of an ordered trajectory

Record each actual stage residual at its source. Repeated occurrences add;
no source is silently discarded. Every weighted forcing budget is exactly the
weighted sum of this profile. Only for a duplicate-free source list does the
squared profile energy equal the original path loss. These statements do not
require idempotence, self-adjointness, or any commutativity.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq C]

/-- Occurrence-summed source residuals, evaluated on the actual trajectory. -/
def realHilbertProjectionSweepSourceResidualProfile
    (P : C → E →L[ℝ] E) : List C → E → C → ℝ :=
  fun sources => List.rec (motive := fun _ => E → C → ℝ)
    (fun _ _ => 0)
    (fun source _ tailProfile x target =>
      (if target = source then ‖x - P source x‖ else 0) + tailProfile (P source x) target)
    sources

/-- Every occurrence contributes a nonnegative genuine stage norm. -/
theorem realHilbertProjectionSweepSourceResidualProfile_nonneg
    (P : C → E →L[ℝ] E) (sources : List C) (x : E) (target : C) :
    0 ≤ realHilbertProjectionSweepSourceResidualProfile P sources x target := by
  induction sources generalizing x with
  | nil => exact le_rfl
  | cons source sources ih =>
      change 0 ≤ (if target = source then ‖x - P source x‖ else 0) +
        realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target
      exact add_nonneg (by split_ifs <;> positivity) (ih (P source x))

/-- Unvisited sources have exactly zero profile. -/
theorem realHilbertProjectionSweepSourceResidualProfile_eq_zero_of_notMem
    (P : C → E →L[ℝ] E) (sources : List C) (x : E) (target : C)
    (hNot : target ∉ sources) :
    realHilbertProjectionSweepSourceResidualProfile P sources x target = 0 := by
  induction sources generalizing x with
  | nil => rfl
  | cons source sources ih =>
      have hNe : target ≠ source := by
        intro h
        exact hNot (List.mem_cons.mpr (Or.inl h))
      have hTail : target ∉ sources := fun h => hNot (List.mem_cons.mpr (Or.inr h))
      change (if target = source then ‖x - P source x‖ else 0) +
        realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target = 0
      rw [if_neg hNe, ih (P source x) hTail, zero_add]

variable [Fintype C]

/-- Exact weighted budget identity, including repeated sources. The weights
need not be nonnegative; no inequality or counting factor is introduced. -/
theorem realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile
    (P : C → E →L[ℝ] E) (weight : C → ℝ) (sources : List C) (x : E) :
    realHilbertProjectionSweepTargetResidualForcingBudget P
        (fun source y => weight source * ‖y - P source y‖) sources x =
      ∑ source : C, weight source * realHilbertProjectionSweepSourceResidualProfile P sources x source := by
  induction sources generalizing x with
  | nil => simp [realHilbertProjectionSweepTargetResidualForcingBudget,
      realHilbertProjectionSweepSourceResidualProfile]
  | cons source sources ih =>
      change weight source * ‖x - P source x‖ +
          realHilbertProjectionSweepTargetResidualForcingBudget P
            (fun next y => weight next * ‖y - P next y‖) sources (P source x) =
        ∑ target : C, weight target * ((if target = source then ‖x - P source x‖ else 0) +
          realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target)
      rw [ih]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp [mul_ite]

/-- Duplicate-free trajectories have exactly the original path-loss energy.
Without Nodup, cross terms from repeated visits must not be dropped. -/
theorem realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss
    (P : C → E →L[ℝ] E) (sources : List C) (x : E) (hNodup : sources.Nodup) :
    (∑ source : C, realHilbertProjectionSweepSourceResidualProfile P sources x source ^ 2) =
      realHilbertProjectionSweepPathLoss P sources x := by
  induction sources generalizing x with
  | nil => simp [realHilbertProjectionSweepSourceResidualProfile, realHilbertProjectionSweepPathLoss]
  | cons source sources ih =>
      have hZero := realHilbertProjectionSweepSourceResidualProfile_eq_zero_of_notMem
        P sources (P source x) source hNodup.notMem
      change (∑ target : C,
          ((if target = source then ‖x - P source x‖ else 0) +
            realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target) ^ 2) =
        ‖x - P source x‖ ^ 2 + realHilbertProjectionSweepPathLoss P sources (P source x)
      calc
        _ = ∑ target : C, ((if target = source then ‖x - P source x‖ ^ 2 else 0) +
            realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target ^ 2) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases hEq : target = source
          · subst target
            simp [hZero]
          · simp [hEq]
        _ = ‖x - P source x‖ ^ 2 +
            ∑ target : C, realHilbertProjectionSweepSourceResidualProfile P sources (P source x) target ^ 2 := by
          rw [Finset.sum_add_distrib]
          simp
        _ = _ := by rw [ih (P source x) hNodup.of_cons]

end
end MGAP4D.MathlibAnalytic
