import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceDegreeIterateDomination
import Mathlib.Tactic

/-!
# Dominate an exact finite heat-bath schedule kernel by a truncated influence kernel

The exact finite schedule kernel is the finite sum of its degree pieces, and for
a schedule without repeated update targets each degree piece is bounded by the
unrestricted influence iterate of the same degree.  Summing those pointwise
bounds gives a coefficient-loss-free domination by the unrestricted truncated
kernel at cutoff equal to the schedule length.

This is finite Dobrushin/path algebra only.  No covariance decay, infinite
Neumann series, continuum clustering, positive physical mass, OS Hamiltonian
gap, or uniform continuum Dobrushin threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A nonnegative influence matrix and a `Nodup` finite update schedule give
pointwise domination of the exact schedule influence kernel by the unrestricted
truncated influence kernel through degree `targets.length`. -/
theorem finiteHeatBathScheduleInfluenceKernel_le_truncated_of_nodup
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (targets : List α)
    (hNodup : targets.Nodup)
    (initial source : α) :
    finiteHeatBathScheduleInfluenceKernel influence targets initial source ≤
      finiteInfluenceTruncatedKernel influence targets.length initial source := by
  rw [finiteHeatBathScheduleInfluenceKernel_eq_sum_degree]
  unfold finiteInfluenceTruncatedKernel
  apply Finset.sum_le_sum
  intro d hd
  exact
    finiteHeatBathScheduleInfluenceDegree_le_iterate_of_nodup
      influence hInfluence d targets hNodup initial source

end

end MathlibAnalytic
end MGAP4D
