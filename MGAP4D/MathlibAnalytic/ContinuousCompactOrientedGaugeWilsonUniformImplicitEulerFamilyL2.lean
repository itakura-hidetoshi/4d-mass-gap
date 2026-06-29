import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerStepL2

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

noncomputable section

/-- The all-time implicit-Euler transfer family.  At time zero it is the
identity; at positive time it is the scaled negative resolvent. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformImplicitEulerL2
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : NNReal) :
    (U.system i).VacuumOrthogonalL2 →L[ℝ]
      (U.system i).VacuumOrthogonalL2 :=
  if ht : t = 0 then
    ContinuousLinearMap.id ℝ (U.system i).VacuumOrthogonalL2
  else
    U.uniformImplicitEulerStepPositiveL2 i (t : ℝ) (by
      exact_mod_cast (pos_iff_ne_zero.mpr ht : 0 < t))

/-- The implicit-Euler family is the identity at time zero. -/
@[simp] theorem continuous_compact_oriented_uniformImplicitEulerL2_zero
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι) :
    U.uniformImplicitEulerL2 i 0 =
      ContinuousLinearMap.id ℝ (U.system i).VacuumOrthogonalL2 := by
  rw [ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformImplicitEulerL2]
  exact dif_pos rfl

/-- At positive NNReal time, the all-time family agrees with the positive-time
scaled resolvent definition. -/
theorem continuous_compact_oriented_uniformImplicitEulerL2_of_pos
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : NNReal)
    (ht : 0 < t) :
    U.uniformImplicitEulerL2 i t =
      U.uniformImplicitEulerStepPositiveL2 i (t : ℝ) (by exact_mod_cast ht) := by
  rw [ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformImplicitEulerL2]
  exact dif_neg (ne_of_gt ht)

/-- Pointwise decay of every finite-volume implicit-Euler transfer family by
one common scalar factor. -/
theorem continuous_compact_oriented_uniformImplicitEulerL2_norm_bound
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : NNReal)
    (y : (U.system i).VacuumOrthogonalL2) :
    ‖U.uniformImplicitEulerL2 i t y‖ ≤
      implicitEulerGapDecayFactor
        (continuousCompactOrientedUniformDobrushinGap U) t * ‖y‖ := by
  by_cases ht : t = 0
  · subst t
    simp [implicitEulerGapDecayFactor]
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    rw [continuous_compact_oriented_uniformImplicitEulerL2_of_pos U i t htpos]
    simpa [implicitEulerGapDecayFactor] using
      continuous_compact_oriented_uniformImplicitEulerStepPositiveL2_norm_bound
        U i (t : ℝ) (by exact_mod_cast htpos) y

/-- Operator-norm decay of the all-time implicit-Euler transfer family. -/
theorem continuous_compact_oriented_uniformImplicitEulerL2_norm_le
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : NNReal) :
    ‖U.uniformImplicitEulerL2 i t‖ ≤
      implicitEulerGapDecayFactor
        (continuousCompactOrientedUniformDobrushinGap U) t := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact implicitEulerGapDecayFactor_nonneg
      (continuous_compact_oriented_uniformDobrushinGap_pos U).le t
  · exact continuous_compact_oriented_uniformImplicitEulerL2_norm_bound U i t

/-- The common implicit-Euler decay factor has the uniform Dobrushin mass as
its positive-time infinitesimal slope. -/
theorem continuous_compact_oriented_uniformImplicitEulerL2_decay_slope
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - implicitEulerGapDecayFactor
            (continuousCompactOrientedUniformDobrushinGap U) t))
      (nhdsWithin 0 (Ioi 0))
      (nhds (continuousCompactOrientedUniformDobrushinGap U)) :=
  continuous_compact_oriented_uniformDobrushin_implicitEuler_slope U

end

end MathlibAnalytic
end MGAP4D
