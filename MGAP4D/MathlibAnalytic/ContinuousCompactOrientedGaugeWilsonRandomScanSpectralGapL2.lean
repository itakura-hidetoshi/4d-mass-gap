import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanVacuumSectorL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The centered Dobrushin Rayleigh estimate restricts to the genuine
Gibbs-vacuum orthogonal sector without an additional centering operator. -/
theorem continuous_compact_oriented_randomScanDobrushin_rayleigh_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : f ∈ C.VacuumOrthogonalL2) :
    inner ℝ (C.randomScanHeatBathL2 f) f ≤
      continuousCompactOrientedDobrushinRandomScanRate C D.coefficient * ‖f‖ ^ 2 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff] at hf
  have hCentered :=
    continuous_compact_oriented_vacuumCenteredL2_eq_self C f hf
  simpa [hCentered] using D.centered_randomScan_rayleigh_le f

/-- On every nonzero vector orthogonal to the Gibbs vacuum, strict Dobrushin
control makes the random-scan Rayleigh quotient strictly smaller than one. -/
theorem continuous_compact_oriented_randomScanDobrushin_rayleigh_lt_norm_sq_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : f ∈ C.VacuumOrthogonalL2)
    (hfNe : f ≠ 0) :
    inner ℝ (C.randomScanHeatBathL2 f) f < ‖f‖ ^ 2 := by
  have hRayleigh :=
    continuous_compact_oriented_randomScanDobrushin_rayleigh_on_vacuumOrthogonal
      C D f hfOrth
  have hRate :
      continuousCompactOrientedDobrushinRandomScanRate C D.coefficient < 1 :=
    continuous_compact_oriented_dobrushinRandomScanRate_lt_one
      C D.coefficient D.coefficient_lt_one D.edgeCard_pos
  have hNorm : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
  have hNormSq : 0 < ‖f‖ ^ 2 := pow_pos hNorm 2
  nlinarith

/-- Under a strict compact Dobrushin certificate, the fixed-point space of the
normalized random-scan operator is exactly the normalized Gibbs-vacuum line. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_eq_self_iff_eq_inner_smul_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.randomScanHeatBathL2 f = f ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 := by
  rw [← continuous_compact_oriented_randomScanDobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    C D f]
  constructor
  · intro hFix
    rw [continuous_compact_oriented_heatBathHamiltonianL2_eq_edgeCard_smul_randomScanDefect
      C D.edgeCard_pos f, hFix, sub_self, smul_zero]
  · intro hZero
    have hCard : (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr D.edgeCard_pos)
    rw [continuous_compact_oriented_heatBathHamiltonianL2_eq_edgeCard_smul_randomScanDefect
      C D.edgeCard_pos f] at hZero
    have hDefect : f - C.randomScanHeatBathL2 f = 0 :=
      (smul_eq_zero.mp hZero).resolve_left hCard
    exact (sub_eq_zero.mp hDefect).symm

/-- The only random-scan fixed vector in the vacuum-orthogonal sector is zero. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_fixed_eq_zero_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : f ∈ C.VacuumOrthogonalL2)
    (hFix : C.randomScanHeatBathL2 f = f) :
    f = 0 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff] at hfOrth
  have hVacuumLine :=
    (continuous_compact_oriented_randomScanHeatBathL2_eq_self_iff_eq_inner_smul_vacuum
      C D f).mp hFix
  rw [hfOrth, zero_smul] at hVacuumLine
  exact hVacuumLine

end

end MathlibAnalytic
end MGAP4D
