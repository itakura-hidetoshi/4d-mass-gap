import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceDegreeReconstruction
import Mathlib.Tactic

/-!
# Dominate schedule degree pieces by unrestricted influence iterates

For a finite heat-bath schedule with no repeated update target, each degree-`d`
contribution of the exact schedule influence kernel is an ordered-subsequence
contribution to the unrestricted degree-`d` influence walk kernel.

The proof avoids an `I + C` stepwise majorization, which would introduce
binomial/path multiplicities.  Instead, in positive degree it records the last
influence edge: its initial vertex must be one of the schedule targets.  For a
`Nodup` schedule, the new head target gives one summand disjoint from all tail
summands.  The resulting finite partial right-convolution sum is then bounded
by the unrestricted right-convolution sum using nonnegativity.

This is finite Dobrushin/path algebra only.  No covariance decay, infinite
Neumann series, continuum clustering, positive physical mass, OS Hamiltonian
gap, or uniform continuum Dobrushin threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- For a nonnegative influence matrix and a schedule without repeated update
targets, every degree piece of the schedule kernel is bounded pointwise by the
unrestricted influence iterate of the same degree. -/
theorem finiteHeatBathScheduleInfluenceDegree_le_iterate_of_nodup
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source) :
    ∀ (d : ℕ) (targets : List α), targets.Nodup →
      ∀ initial source : α,
        finiteHeatBathScheduleInfluenceDegree influence targets d initial source ≤
          finiteInfluenceIterateKernel influence d initial source := by
  intro d
  induction d with
  | zero =>
      intro targets
      induction targets with
      | nil =>
          intro _ initial source
          simp [finiteHeatBathScheduleInfluenceDegree,
            finiteInfluenceIterateKernel]
      | cons target targets ihTargets =>
          intro hNodup initial source
          have htailNodup : targets.Nodup :=
            (List.nodup_cons.mp hNodup).2
          rw [finiteHeatBathScheduleInfluenceDegree_cons_zero]
          by_cases hsource : source = target
          · subst source
            by_cases hinitial : initial = target <;>
              simp [finiteInfluenceIterateKernel, hinitial]
          · simp only [hsource, if_false]
            exact ihTargets htailNodup initial source
  | succ d ihDegree =>
      intro targets hNodup initial source
      have hterminal :
          ∀ (schedule : List α), schedule.Nodup →
            ∀ initial source : α,
              finiteHeatBathScheduleInfluenceDegree influence schedule (d + 1)
                  initial source ≤
                ∑ mid ∈ schedule.toFinset,
                  finiteInfluenceIterateKernel influence d initial mid *
                    influence mid source := by
        intro schedule
        induction schedule with
        | nil =>
            intro _ initial source
            simp
        | cons target tail ihTail =>
            intro hScheduleNodup initial source
            have hparts := List.nodup_cons.mp hScheduleNodup
            have htargetNotMem : target ∉ tail := hparts.1
            have htailNodup : tail.Nodup := hparts.2
            rw [finiteHeatBathScheduleInfluenceDegree_cons_succ]
            by_cases hsource : source = target
            · simp only [hsource, if_true]
              exact
                Finset.sum_nonneg fun mid _ =>
                  mul_nonneg
                    (finiteInfluenceIterateKernel_nonneg
                      influence hInfluence d initial mid)
                    (hInfluence mid source)
            · simp only [hsource, if_false]
              calc
                finiteHeatBathScheduleInfluenceDegree influence tail (d + 1)
                      initial source +
                    influence target source *
                      finiteHeatBathScheduleInfluenceDegree influence tail d
                        initial target ≤
                    (∑ mid ∈ tail.toFinset,
                        finiteInfluenceIterateKernel influence d initial mid *
                          influence mid source) +
                      influence target source *
                        finiteInfluenceIterateKernel influence d initial target := by
                  exact
                    add_le_add
                      (ihTail htailNodup initial source)
                      (mul_le_mul_of_nonneg_left
                        (ihDegree tail htailNodup initial target)
                        (hInfluence target source))
                _ =
                    ∑ mid ∈ (target :: tail).toFinset,
                      finiteInfluenceIterateKernel influence d initial mid *
                        influence mid source := by
                  have htargetNotMemFinset : target ∉ tail.toFinset := by
                    simpa using htargetNotMem
                  rw [List.toFinset_cons, Finset.sum_insert htargetNotMemFinset]
                  ring
      calc
        finiteHeatBathScheduleInfluenceDegree influence targets (d + 1)
              initial source ≤
            ∑ mid ∈ targets.toFinset,
              finiteInfluenceIterateKernel influence d initial mid *
                influence mid source :=
          hterminal targets hNodup initial source
        _ ≤
            ∑ mid : α,
              finiteInfluenceIterateKernel influence d initial mid *
                influence mid source := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.subset_univ _
          · intro mid _ _
            exact
              mul_nonneg
                (finiteInfluenceIterateKernel_nonneg
                  influence hInfluence d initial mid)
                (hInfluence mid source)
        _ = finiteInfluenceIterateKernel influence (d + 1) initial source := by
          exact (finiteInfluenceIterateKernel_succ_right
            influence d initial source).symm

end

end MathlibAnalytic
end MGAP4D
