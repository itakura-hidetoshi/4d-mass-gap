import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonVacuumOrthogonalOperatorsL2
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The bounded energy form induced by the native heat-bath operator on the
Gibbs-vacuum orthogonal Hilbert sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyFormL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 →L[ℝ] ℝ :=
  (innerSL ℝ).comp C.heatBathHamiltonianVacuumOrthogonalL2

@[simp] theorem continuous_compact_oriented_restrictedEnergyFormL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.VacuumOrthogonalL2) :
    C.restrictedEnergyFormL2 f g =
      inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) g :=
  rfl

/-- The strict Dobrushin gap makes the restricted energy form coercive. -/
theorem continuous_compact_oriented_restrictedEnergyFormL2_isCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    IsCoercive C.restrictedEnergyFormL2 := by
  refine ⟨continuousCompactOrientedDobrushinHeatBathGap D.coefficient, ?_, ?_⟩
  · unfold continuousCompactOrientedDobrushinHeatBathGap
    exact sub_pos.mpr D.coefficient_lt_one
  · intro f
    have hGap :=
      continuous_compact_oriented_randomScanDobrushinHamiltonianL2_gap_on_vacuumOrthogonal
        C D (f : Lp ℝ 2 C.gibbsMeasure)
        ((continuous_compact_oriented_mem_vacuumOrthogonalL2_iff
          C (f : Lp ℝ 2 C.gibbsMeasure)).mp f.property)
    change
      continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖f‖ * ‖f‖ ≤
        inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) f
    change
      continuousCompactOrientedDobrushinHeatBathGap D.coefficient *
          ‖(f : Lp ℝ 2 C.gibbsMeasure)‖ *
          ‖(f : Lp ℝ 2 C.gibbsMeasure)‖ ≤
        inner ℝ
          (C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure))
          (f : Lp ℝ 2 C.gibbsMeasure)
    simpa [pow_two] using hGap

end

end MathlibAnalytic
end MGAP4D
