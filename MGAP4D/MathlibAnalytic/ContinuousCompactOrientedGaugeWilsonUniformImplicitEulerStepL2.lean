import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonImplicitEulerGapSlopeL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A negative real spectral parameter selected by a positive implicit-Euler
time step lies below the uniform Dobrushin gap. -/
theorem continuous_compact_oriented_uniformDobrushin_neg_inv_lt_gap
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    {t : ℝ}
    (ht : 0 < t) :
    -t⁻¹ < continuousCompactOrientedUniformDobrushinGap U := by
  have hgap := continuous_compact_oriented_uniformDobrushinGap_pos U
  have hinv : 0 < t⁻¹ := inv_pos.mpr ht
  linarith

/-- The positive-time implicit-Euler transfer step on a finite-volume
excitation Hilbert sector:

`J_t = t⁻¹ (H + t⁻¹ I)⁻¹ = (I + t H)⁻¹`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformImplicitEulerStepPositiveL2
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : ℝ)
    (ht : 0 < t) :
    (U.system i).VacuumOrthogonalL2 →L[ℝ]
      (U.system i).VacuumOrthogonalL2 :=
  t⁻¹ • U.uniformResolventL2 i
    (continuous_compact_oriented_uniformDobrushin_neg_inv_lt_gap U ht)

@[simp] theorem continuous_compact_oriented_uniformImplicitEulerStepPositiveL2_apply
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : ℝ)
    (ht : 0 < t)
    (y : (U.system i).VacuumOrthogonalL2) :
    U.uniformImplicitEulerStepPositiveL2 i t ht y =
      t⁻¹ • U.uniformResolventL2 i
        (continuous_compact_oriented_uniformDobrushin_neg_inv_lt_gap U ht) y :=
  rfl

/-- Scalar identity underlying the implicit-Euler resolvent estimate. -/
theorem inv_mul_inv_add_inv_eq_inv_one_add_mul
    {mass t : ℝ}
    (ht : 0 < t)
    (hmass : 0 ≤ mass) :
    t⁻¹ * (mass + t⁻¹)⁻¹ = (1 + mass * t)⁻¹ := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hdenpos : 0 < 1 + mass * t := by
    nlinarith [mul_nonneg hmass ht.le]
  have hdenne : 1 + mass * t ≠ 0 := ne_of_gt hdenpos
  field_simp [htne, hdenne]
  ring

/-- Pointwise implicit-Euler contraction with the uniform Dobrushin decay
factor. -/
theorem continuous_compact_oriented_uniformImplicitEulerStepPositiveL2_norm_bound
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : ℝ)
    (ht : 0 < t)
    (y : (U.system i).VacuumOrthogonalL2) :
    ‖U.uniformImplicitEulerStepPositiveL2 i t ht y‖ ≤
      (1 + continuousCompactOrientedUniformDobrushinGap U * t)⁻¹ * ‖y‖ := by
  let hlocal :=
    continuous_compact_oriented_uniformDobrushin_neg_inv_lt_gap U ht
  have hR :=
    continuous_compact_oriented_uniformResolventL2_norm_bound
      U i hlocal y
  have hinvNonneg : 0 ≤ t⁻¹ := (inv_pos.mpr ht).le
  rw [continuous_compact_oriented_uniformImplicitEulerStepPositiveL2_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    t⁻¹ * ‖U.uniformResolventL2 i hlocal y‖ ≤
        t⁻¹ *
          ((continuousCompactOrientedUniformDobrushinGap U - (-t⁻¹))⁻¹ *
            ‖y‖) :=
      mul_le_mul_of_nonneg_left hR hinvNonneg
    _ =
        (1 + continuousCompactOrientedUniformDobrushinGap U * t)⁻¹ * ‖y‖ := by
      rw [sub_neg_eq_add, ← mul_assoc,
        inv_mul_inv_add_inv_eq_inv_one_add_mul ht
          (continuous_compact_oriented_uniformDobrushinGap_pos U).le]

/-- Operator-norm form of the positive-time implicit-Euler contraction. -/
theorem continuous_compact_oriented_uniformImplicitEulerStepPositiveL2_norm_le
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (t : ℝ)
    (ht : 0 < t) :
    ‖U.uniformImplicitEulerStepPositiveL2 i t ht‖ ≤
      (1 + continuousCompactOrientedUniformDobrushinGap U * t)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply inv_nonneg.mpr
    exact add_nonneg zero_le_one
      (mul_nonneg
        (continuous_compact_oriented_uniformDobrushinGap_pos U).le ht.le)
  · exact
      continuous_compact_oriented_uniformImplicitEulerStepPositiveL2_norm_bound
        U i t ht

end

end MathlibAnalytic
end MGAP4D
