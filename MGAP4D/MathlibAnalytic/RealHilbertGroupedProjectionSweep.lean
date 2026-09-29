import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathProjectionSweepL2
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Grouped ordered sweeps of nonexpansive linear maps

Reindexing and flattening preserve the actual order. The displacement estimate
uses every group residual at the ORIGINAL input. It telescopes contractions,
not successive residuals with an implicit cardinality multiplier.
-/

namespace MGAP4D.MathlibAnalytic.GroupedProjectionSweep

noncomputable section

variable {E I C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A composition of norm contractions is a norm contraction. -/
theorem norm_le (P : I → E →L[ℝ] E)
    (hP : ∀ i x, ‖P i x‖ ≤ ‖x‖) (xs : List I) (x : E) :
    ‖realHilbertProjectionSweep P xs x‖ ≤ ‖x‖ := by
  induction xs generalizing x with
  | nil => exact le_rfl
  | cons i xs ih => exact (ih (P i x)).trans (hP i x)

/-- Concatenation acts in the original first-list-then-second-list order. -/
theorem append_apply (P : I → E →L[ℝ] E) (xs ys : List I) (x : E) :
    realHilbertProjectionSweep P (xs ++ ys) x =
      realHilbertProjectionSweep P ys (realHilbertProjectionSweep P xs x) := by
  induction xs generalizing x with
  | nil => rfl
  | cons i xs ih => exact ih (P i x)

/-- Reindex a list without permuting its operators. -/
theorem map_apply (P : I → E →L[ℝ] E) (index : C → I) (cs : List C) (x : E) :
    realHilbertProjectionSweep P (cs.map index) x =
      realHilbertProjectionSweep (fun c => P (index c)) cs x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => exact ih (P (index c) x)

/-- Flattening groups is exactly composition of their ordered sweeps. -/
theorem flatMap_apply (P : I → E →L[ℝ] E) (groups : C → List I)
    (cs : List C) (x : E) :
    realHilbertProjectionSweep P (cs.flatMap groups) x =
      realHilbertProjectionSweep (fun c => realHilbertProjectionSweep P (groups c)) cs x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
      rw [List.flatMap_cons, append_apply]
      exact ih (realHilbertProjectionSweep P (groups c) x)

/-- Original-input telescope. No commutativity or idempotence is required. -/
theorem displacement_le_sum_initial (P : C → E →L[ℝ] E)
    (hP : ∀ c x, ‖P c x‖ ≤ ‖x‖) (cs : List C) (x : E) :
    ‖x - realHilbertProjectionSweep P cs x‖ ≤
      (cs.map (fun c => ‖x - P c x‖)).sum := by
  induction cs with
  | nil => simp [realHilbertProjectionSweep]
  | cons c cs ih =>
      let T := realHilbertProjectionSweep P cs
      have hTail : ‖T x - T (P c x)‖ ≤ ‖x - P c x‖ := by
        rw [← map_sub]
        exact norm_le P hP cs (x - P c x)
      have hTriangle : ‖x - T (P c x)‖ ≤ ‖x - T x‖ + ‖T x - T (P c x)‖ := by
        simpa only [dist_eq_norm] using dist_triangle x (T x) (T (P c x))
      change ‖x - T (P c x)‖ ≤ ‖x - P c x‖ + (cs.map (fun d => ‖x - P d x‖)).sum
      exact (hTriangle.trans (_root_.add_le_add ih hTail)).trans_eq (add_comm _ _)

end
end MGAP4D.MathlibAnalytic.GroupedProjectionSweep
