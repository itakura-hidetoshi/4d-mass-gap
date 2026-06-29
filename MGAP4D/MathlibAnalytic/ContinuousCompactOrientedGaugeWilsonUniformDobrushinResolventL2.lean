import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyResolventL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A spectral parameter below the uniform family gap lies below every local
Dobrushin gap. -/
theorem continuous_compact_oriented_uniformDobrushin_lambda_lt_localGap
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    lambda < continuousCompactOrientedDobrushinHeatBathGap
      (U.certificate i).coefficient :=
  hlambda.trans_le
    (continuous_compact_oriented_uniformDobrushinGap_le_localGap U i)

/-- The local resolvent, canonically selected using the uniform family gap. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformResolventL2
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    (U.system i).VacuumOrthogonalL2 →L[ℝ]
      (U.system i).VacuumOrthogonalL2 :=
  (U.system i).restrictedEnergyResolventL2
    (U.certificate i)
    (continuous_compact_oriented_uniformDobrushin_lambda_lt_localGap
      U i hlambda)

/-- The uniformly selected resolvent is a right inverse of every shifted
restricted Hamiltonian. -/
theorem continuous_compact_oriented_uniformResolvent_shift_apply
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U)
    (y : (U.system i).VacuumOrthogonalL2) :
    (U.system i).restrictedEnergyShiftL2 lambda
        (U.uniformResolventL2 i hlambda y) = y := by
  unfold
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformResolventL2
  exact
    continuous_compact_oriented_restrictedEnergyShift_apply_resolvent
      (U.system i) (U.certificate i)
      (continuous_compact_oriented_uniformDobrushin_lambda_lt_localGap
        U i hlambda) y

/-- The uniformly selected resolvent is a left inverse of every shifted
restricted Hamiltonian. -/
theorem continuous_compact_oriented_uniformResolvent_apply_shift
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U)
    (f : (U.system i).VacuumOrthogonalL2) :
    U.uniformResolventL2 i hlambda
        ((U.system i).restrictedEnergyShiftL2 lambda f) = f := by
  unfold
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformResolventL2
  exact
    continuous_compact_oriented_restrictedEnergyResolvent_apply_shift
      (U.system i) (U.certificate i)
      (continuous_compact_oriented_uniformDobrushin_lambda_lt_localGap
        U i hlambda) f

/-- Every shifted restricted Hamiltonian below the uniform family gap is
bijective. -/
theorem continuous_compact_oriented_uniformDobrushin_shift_bijective
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    Function.Bijective ((U.system i).restrictedEnergyShiftL2 lambda) := by
  constructor
  · intro f g hfg
    calc
      f = U.uniformResolventL2 i hlambda
          ((U.system i).restrictedEnergyShiftL2 lambda f) :=
        (continuous_compact_oriented_uniformResolvent_apply_shift
          U i hlambda f).symm
      _ = U.uniformResolventL2 i hlambda
          ((U.system i).restrictedEnergyShiftL2 lambda g) := by rw [hfg]
      _ = g :=
        continuous_compact_oriented_uniformResolvent_apply_shift
          U i hlambda g
  · intro y
    exact
      ⟨U.uniformResolventL2 i hlambda y,
        continuous_compact_oriented_uniformResolvent_shift_apply
          U i hlambda y⟩

end

end MathlibAnalytic
end MGAP4D
