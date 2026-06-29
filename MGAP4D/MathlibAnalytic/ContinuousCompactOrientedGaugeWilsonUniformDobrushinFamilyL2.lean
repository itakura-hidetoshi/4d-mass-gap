import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyShiftCoerciveL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- An indexed compact Wilson family whose scale-dependent Dobrushin
certificates are dominated by one strict coefficient. -/
structure ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData
    (ι : Type*) where
  system : ι → ContinuousCompactOrientedGaugeWilsonSystem
  certificate : (i : ι) →
    ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate
      (system i)
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  coefficient_le : ∀ i, (certificate i).coefficient ≤ coefficientBound

/-- The scale-independent heat-bath gap carried by a uniform Dobrushin
family. -/
def continuousCompactOrientedUniformDobrushinGap
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι) : ℝ :=
  1 - U.coefficientBound

/-- The uniform Dobrushin gap is strictly positive. -/
theorem continuous_compact_oriented_uniformDobrushinGap_pos
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι) :
    0 < continuousCompactOrientedUniformDobrushinGap U := by
  unfold continuousCompactOrientedUniformDobrushinGap
  exact sub_pos.mpr U.coefficientBound_lt_one

/-- Every scale-dependent Dobrushin gap dominates the uniform family gap. -/
theorem continuous_compact_oriented_uniformDobrushinGap_le_localGap
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι) :
    continuousCompactOrientedUniformDobrushinGap U ≤
      continuousCompactOrientedDobrushinHeatBathGap
        (U.certificate i).coefficient := by
  unfold continuousCompactOrientedUniformDobrushinGap
  unfold continuousCompactOrientedDobrushinHeatBathGap
  linarith [U.coefficient_le i]

/-- The restricted native Hamiltonians have one coercivity constant at every
scale of the indexed compact Wilson family. -/
theorem continuous_compact_oriented_uniformDobrushin_restrictedEnergy_gap
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (f : (U.system i).VacuumOrthogonalL2) :
    continuousCompactOrientedUniformDobrushinGap U * ‖f‖ ^ 2 ≤
      inner ℝ ((U.system i).heatBathHamiltonianVacuumOrthogonalL2 f) f := by
  calc
    continuousCompactOrientedUniformDobrushinGap U * ‖f‖ ^ 2 ≤
        continuousCompactOrientedDobrushinHeatBathGap
            (U.certificate i).coefficient * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (continuous_compact_oriented_uniformDobrushinGap_le_localGap U i)
        (sq_nonneg ‖f‖)
    _ ≤ inner ℝ
          ((U.system i).heatBathHamiltonianVacuumOrthogonalL2 f) f :=
      continuous_compact_oriented_restrictedEnergy_gap
        (U.system i) (U.certificate i) f

/-- Every real shift below the uniform family gap is uniformly coercive. -/
theorem continuous_compact_oriented_uniformDobrushin_restrictedEnergyShift_gap
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    (lambda : ℝ)
    (f : (U.system i).VacuumOrthogonalL2) :
    (continuousCompactOrientedUniformDobrushinGap U - lambda) * ‖f‖ ^ 2 ≤
      inner ℝ ((U.system i).restrictedEnergyShiftL2 lambda f) f := by
  calc
    (continuousCompactOrientedUniformDobrushinGap U - lambda) * ‖f‖ ^ 2 ≤
        (continuousCompactOrientedDobrushinHeatBathGap
            (U.certificate i).coefficient - lambda) * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (sub_le_sub_right
          (continuous_compact_oriented_uniformDobrushinGap_le_localGap U i)
          lambda)
        (sq_nonneg ‖f‖)
    _ ≤ inner ℝ ((U.system i).restrictedEnergyShiftL2 lambda f) f :=
      continuous_compact_oriented_restrictedEnergyShiftL2_gap
        (U.system i) (U.certificate i) lambda f

end

end MathlibAnalytic
end MGAP4D
