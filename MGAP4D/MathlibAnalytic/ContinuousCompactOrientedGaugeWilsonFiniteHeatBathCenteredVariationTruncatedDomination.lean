import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceTruncatedDomination
import Mathlib.Tactic

/-!
# Truncated unrestricted influence bound for the actual finite heat-bath variation

The exact finite heat-bath centered variation profile already admits a linear
representation by the prescribed schedule influence kernel.  For a `Nodup`
schedule, the schedule kernel is coefficient-loss-free dominated by the
unrestricted influence kernel truncated at the schedule length.  Combining
those facts with nonnegativity of the initial centered variation profile gives
a direct bound for the actual finite heat-bath variation.

This is finite-volume heat-bath/Dobrushin algebra only.  Update count is not
Euclidean time.  No covariance decay, infinite Neumann series, continuum
clustering, positive physical mass, OS Hamiltonian gap, or uniform continuum
Dobrushin threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- For a `Nodup` finite heat-bath schedule, the actual centered variation after
that schedule is bounded by the unrestricted truncated influence kernel acting
on the initial variation profile. -/
theorem continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation_le_sum_truncatedInfluenceKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (targets : List C.base.geometry.Edge)
    (hNodup : targets.Nodup)
    (source : C.base.geometry.Edge) :
    (P.finiteHeatBathCenteredVariationProfile D targets).variation source ≤
      ∑ initial : C.base.geometry.Edge,
        finiteInfluenceTruncatedKernel D.influence targets.length initial source *
          P.variation initial := by
  rw [continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation_eq_sum_scheduleInfluenceKernel]
  apply Finset.sum_le_sum
  intro initial _
  exact
    mul_le_mul_of_nonneg_right
      (finiteHeatBathScheduleInfluenceKernel_le_truncated_of_nodup
        D.influence D.influence_nonneg targets hNodup initial source)
      (P.variation_nonneg initial)

end

end MathlibAnalytic
end MGAP4D
