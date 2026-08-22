import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceTruncatedDomination
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentInfluenceGeometricTail
import Mathlib.Tactic

/-!
# Geometric domination of finite heat-bath schedule influence after a zero prefix

The exact finite heat-bath schedule kernel is already dominated, for a `Nodup`
schedule, by the unrestricted truncated influence kernel through the schedule
length.  The current same-root Dobrushin route also bounds every finite tail of
unrestricted influence iterates by the full geometric tail.

This file composes those two facts when the unrestricted iterate prefix below a
degree `D` vanishes exactly.  If the schedule length is `D + M`, the truncated
kernel splits into that zero prefix and the finite tail beginning at `D`, hence
the exact schedule kernel inherits the geometric factor
`coefficient^D / (1 - coefficient)` with no schedule-multiplicity loss.

This is still finite Dobrushin/path algebra.  No covariance representation,
continuum clustering, positive physical mass, OS Hamiltonian gap, or uniform
factorial-continuum Dobrushin threshold is asserted here.  Heat-bath update
count is not identified with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- If unrestricted influence iterates vanish through the complete prefix below
`D`, then any `Nodup` finite heat-bath schedule of length `D + M` is bounded by
the full strict-Dobrushin geometric tail beginning at degree `D`. -/
theorem
    continuous_compact_oriented_dobrushin_finiteHeatBathScheduleInfluenceKernel_le_geometric_of_nodup_prefix_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (data : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hStrict : data.coefficient < 1)
    (D M : ℕ)
    (targets : List C.base.geometry.Edge)
    (hNodup : targets.Nodup)
    (hLength : targets.length = D + M)
    (initial source : C.base.geometry.Edge)
    (hPrefix :
      (∑ d ∈ Finset.range D,
        finiteInfluenceIterateKernel data.influence d initial source) = 0) :
    finiteHeatBathScheduleInfluenceKernel
        data.influence targets initial source ≤
      data.coefficient ^ D / (1 - data.coefficient) := by
  have hSchedule :=
    finiteHeatBathScheduleInfluenceKernel_le_truncated_of_nodup
      data.influence data.influence_nonneg targets hNodup initial source
  have hTruncated :
      finiteInfluenceTruncatedKernel
          data.influence (D + M) initial source ≤
        data.coefficient ^ D / (1 - data.coefficient) := by
    have hSplit :
        finiteInfluenceTruncatedKernel
            data.influence (D + M) initial source =
          (∑ d ∈ Finset.range D,
            finiteInfluenceIterateKernel data.influence d initial source) +
          ∑ k ∈ Finset.range (M + 1),
            finiteInfluenceIterateKernel
              data.influence (D + k) initial source := by
      unfold finiteInfluenceTruncatedKernel
      rw [show D + M + 1 = D + (M + 1) by omega]
      rw [Finset.sum_range_add]
    rw [hSplit, hPrefix, zero_add]
    exact
      continuous_compact_oriented_dobrushin_influenceIterateKernel_tail_le_geometric
        C data hStrict D (M + 1) initial source
  rw [hLength] at hSchedule
  exact hSchedule.trans hTruncated

end

end MathlibAnalytic
end MGAP4D
