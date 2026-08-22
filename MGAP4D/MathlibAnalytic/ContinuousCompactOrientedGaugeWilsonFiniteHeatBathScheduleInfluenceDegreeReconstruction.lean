import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceDegree
import Mathlib.Tactic

/-!
# Reconstruct the exact finite heat-bath schedule kernel from degree pieces

The exact finite heat-bath schedule influence kernel has now been refined by the
number of influence edges used.  This file closes the finite reconstruction:
the exact schedule kernel is the sum of its degree pieces from degree zero
through the schedule length.

The only endpoint bookkeeping needed in the cons step is the finite-support
statement from the degree layer: a tail schedule of length `L` contributes zero
in degree `L + 1`.  No unrestricted-walk comparison is made here; that remains
a separate ordered-subsequence/path-injection step.

This is finite Dobrushin/path algebra only.  No covariance decay, infinite
Neumann series, continuum clustering, positive physical mass, OS Hamiltonian
gap, or uniform continuum Dobrushin threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- For a source not equal to the newly updated target, summing all degree
pieces of the cons schedule gives the tail sum plus one terminal influence edge
times the tail sum ending at the target. -/
theorem finiteHeatBathScheduleInfluenceDegree_sum_cons_of_ne
    {α : Type*}
    [DecidableEq α]
    (influence : α → α → ℝ)
    (target : α)
    (targets : List α)
    (initial source : α)
    (h : source ≠ target) :
    (∑ d ∈ Finset.range ((target :: targets).length + 1),
        finiteHeatBathScheduleInfluenceDegree influence (target :: targets) d
          initial source) =
      (∑ d ∈ Finset.range (targets.length + 1),
          finiteHeatBathScheduleInfluenceDegree influence targets d initial source) +
        influence target source *
          (∑ d ∈ Finset.range (targets.length + 1),
            finiteHeatBathScheduleInfluenceDegree influence targets d initial target) := by
  have htop :
      finiteHeatBathScheduleInfluenceDegree influence targets
          (targets.length + 1) initial source = 0 := by
    exact
      finiteHeatBathScheduleInfluenceDegree_eq_zero_of_length_lt
        influence targets (targets.length + 1) initial source (by omega)
  have hsource :
      finiteHeatBathScheduleInfluenceDegree influence targets 0 initial source +
          (∑ d ∈ Finset.range (targets.length + 1),
            finiteHeatBathScheduleInfluenceDegree influence targets (d + 1)
              initial source) =
        ∑ d ∈ Finset.range (targets.length + 1),
          finiteHeatBathScheduleInfluenceDegree influence targets d initial source := by
    rw [Finset.sum_range_succ, htop, add_zero]
    rw [Finset.sum_range_succ']
    ac_rfl
  simp only [List.length_cons]
  rw [show targets.length + 1 + 1 = (targets.length + 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  simp only [finiteHeatBathScheduleInfluenceDegree_cons_zero,
    finiteHeatBathScheduleInfluenceDegree_cons_succ, h, if_false]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [← hsource]
  ring

/-- The exact schedule influence kernel is precisely the finite sum of its
degree pieces, with maximal possible degree equal to the schedule length. -/
theorem finiteHeatBathScheduleInfluenceKernel_eq_sum_degree
    {α : Type*}
    [DecidableEq α]
    (influence : α → α → ℝ) :
    ∀ (targets : List α) (initial source : α),
      finiteHeatBathScheduleInfluenceKernel influence targets initial source =
        ∑ d ∈ Finset.range (targets.length + 1),
          finiteHeatBathScheduleInfluenceDegree influence targets d initial source := by
  intro targets
  induction targets with
  | nil =>
      intro initial source
      simp [finiteHeatBathScheduleInfluenceKernel,
        finiteHeatBathScheduleInfluenceDegree]
  | cons target targets ih =>
      intro initial source
      rw [finiteHeatBathScheduleInfluenceKernel_cons]
      by_cases h : source = target
      · subst source
        simp [finiteHeatBathScheduleInfluenceDegree]
      · simp only [h, if_false]
        rw [ih initial source, ih initial target]
        exact
          (finiteHeatBathScheduleInfluenceDegree_sum_cons_of_ne
            influence target targets initial source h).symm

end

end MathlibAnalytic
end MGAP4D
