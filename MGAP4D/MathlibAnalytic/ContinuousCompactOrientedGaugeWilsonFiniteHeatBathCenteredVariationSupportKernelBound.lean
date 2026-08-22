import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceKernel
import Mathlib.Tactic

/-!
# Support-kernel bounds for actual finite heat-bath centered variation

The current Feller closure already identifies the centered variation profile
after an arbitrary finite ordered heat-bath schedule with the exact linear
action of the schedule influence kernel on the initial variation profile.

This file packages the elementary support reduction needed to turn any
pointwise schedule-kernel estimate into an actual observable-variation bound.
If the initial variation vanishes outside a finite support `S`, and every
schedule-kernel entry from `S` to a fixed output source is at most `b`, then the
updated centered variation at that source is at most

`b * ∑ initial ∈ S, P.variation initial`.

No geometric estimate is introduced here; the bound `b` is deliberately left
abstract so that the periodic separated-support geometric theorem can be
inserted in the next same-root layer without duplicating Feller bookkeeping.

This remains finite-volume heat-bath/Dobrushin algebra.  Update count is not
Euclidean time.  No covariance decay, continuum clustering, positive physical
mass, OS Hamiltonian gap, or uniform factorial-continuum Dobrushin threshold is
asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A pointwise bound on the exact schedule influence kernel over the finite
support of the initial centered variation profile gives the corresponding
actual finite heat-bath centered-variation bound. -/
theorem
    continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation_le_support_sum_mul_of_scheduleInfluenceKernel_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (S : Finset C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (source : C.base.geometry.Edge)
    (b : ℝ)
    (hSupport : ∀ initial : C.base.geometry.Edge,
      initial ∉ S → P.variation initial = 0)
    (hKernel : ∀ initial : C.base.geometry.Edge, initial ∈ S →
      finiteHeatBathScheduleInfluenceKernel
        D.influence targets initial source ≤ b) :
    (P.finiteHeatBathCenteredVariationProfile D targets).variation source ≤
      b * ∑ initial ∈ S, P.variation initial := by
  classical
  rw [continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation_eq_sum_scheduleInfluenceKernel]
  have hRestrict :
      (∑ initial ∈ S,
        finiteHeatBathScheduleInfluenceKernel
            D.influence targets initial source * P.variation initial) =
        ∑ initial : C.base.geometry.Edge,
          finiteHeatBathScheduleInfluenceKernel
              D.influence targets initial source * P.variation initial := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro initial _ hNotMem
    rw [hSupport initial hNotMem, mul_zero]
  rw [← hRestrict]
  calc
    (∑ initial ∈ S,
        finiteHeatBathScheduleInfluenceKernel
            D.influence targets initial source * P.variation initial) ≤
      ∑ initial ∈ S, b * P.variation initial := by
        apply Finset.sum_le_sum
        intro initial hInitial
        exact
          mul_le_mul_of_nonneg_right
            (hKernel initial hInitial)
            (P.variation_nonneg initial)
    _ = b * ∑ initial ∈ S, P.variation initial := by
      rw [Finset.mul_sum]

end

end MathlibAnalytic
end MGAP4D
