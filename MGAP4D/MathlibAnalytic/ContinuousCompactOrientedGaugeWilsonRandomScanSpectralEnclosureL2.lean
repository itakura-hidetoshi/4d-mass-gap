import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanPositiveContractionL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanSpectralGapL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- For a nonnegative Dobrushin coefficient and a nonempty physical-link set,
the normalized random-scan rate is nonnegative. -/
theorem continuous_compact_oriented_dobrushinRandomScanRate_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (coefficient : ℝ)
    (hCoefficient : 0 ≤ coefficient)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    0 ≤ continuousCompactOrientedDobrushinRandomScanRate C coefficient := by
  have hCardPos :
      0 < (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hCardOneNat : 1 ≤ Fintype.card C.base.geometry.Edge :=
    Nat.succ_le_iff.mpr hEdge
  have hCardOne :
      (1 : ℝ) ≤ (Fintype.card C.base.geometry.Edge : ℝ) := by
    exact_mod_cast hCardOneNat
  have hGapLeOne :
      continuousCompactOrientedDobrushinHeatBathGap coefficient ≤ 1 := by
    unfold continuousCompactOrientedDobrushinHeatBathGap
    linarith
  have hGapLeCard :
      continuousCompactOrientedDobrushinHeatBathGap coefficient ≤
        (Fintype.card C.base.geometry.Edge : ℝ) :=
    hGapLeOne.trans hCardOne
  have hDivLeOne :
      continuousCompactOrientedDobrushinHeatBathGap coefficient /
          (Fintype.card C.base.geometry.Edge : ℝ) ≤ 1 :=
    (div_le_one hCardPos).2 hGapLeCard
  unfold continuousCompactOrientedDobrushinRandomScanRate
  linarith

/-- Under a strict Dobrushin random-scan certificate, the normalized rate lies
in the half-open unit interval. -/
theorem continuous_compact_oriented_dobrushinRandomScanRate_mem_unitInterval
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    0 ≤ continuousCompactOrientedDobrushinRandomScanRate C D.coefficient ∧
      continuousCompactOrientedDobrushinRandomScanRate C D.coefficient < 1 :=
  ⟨continuous_compact_oriented_dobrushinRandomScanRate_nonneg
      C D.coefficient D.coefficient_nonneg D.edgeCard_pos,
    continuous_compact_oriented_dobrushinRandomScanRate_lt_one
      C D.coefficient D.coefficient_lt_one D.edgeCard_pos⟩

/-- On the Gibbs-vacuum orthogonal sector, the random-scan quadratic form lies
between zero and the strict Dobrushin rate. -/
theorem continuous_compact_oriented_randomScanDobrushin_quadraticForm_bounds_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : f ∈ C.VacuumOrthogonalL2) :
    0 ≤ inner ℝ (C.randomScanHeatBathL2 f) f ∧
      inner ℝ (C.randomScanHeatBathL2 f) f ≤
        continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
          ‖f‖ ^ 2 :=
  ⟨continuous_compact_oriented_randomScanHeatBathL2_nonneg
      C D.edgeCard_pos f,
    continuous_compact_oriented_randomScanDobrushin_rayleigh_on_vacuumOrthogonal
      C D f hfOrth⟩

/-- The normalized random-scan defect has the explicit Dobrushin coercivity
constant on the Gibbs-vacuum orthogonal sector. -/
theorem continuous_compact_oriented_randomScanDobrushin_defect_gap_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : f ∈ C.VacuumOrthogonalL2) :
    (1 - continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) *
        ‖f‖ ^ 2 ≤
      ‖f‖ ^ 2 - inner ℝ (C.randomScanHeatBathL2 f) f := by
  have hRayleigh :=
    continuous_compact_oriented_randomScanDobrushin_rayleigh_on_vacuumOrthogonal
      C D f hfOrth
  nlinarith [sq_nonneg ‖f‖]

/-- Positivity of random scan gives the natural edge-cardinality upper bound
for the unnormalized heat-bath Hamiltonian. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_inner_le_edgeCard_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f ≤
      (Fintype.card C.base.geometry.Edge : ℝ) * ‖f‖ ^ 2 := by
  have hRandomNonneg :=
    continuous_compact_oriented_randomScanHeatBathL2_nonneg C hEdge f
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_eq_edgeCard_mul_randomScanDefect
    C hEdge f]
  have hCardNonneg :
      0 ≤ (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_nonneg _
  nlinarith

/-- Finite-volume spectral enclosure in quadratic-form language: on the
Gibbs-vacuum orthogonal sector, the native heat-bath Hamiltonian lies between
the positive Dobrushin gap and the edge-cardinality ultraviolet bound. -/
theorem continuous_compact_oriented_randomScanDobrushinHamiltonianL2_quadraticForm_bounds_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : f ∈ C.VacuumOrthogonalL2) :
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖f‖ ^ 2 ≤
        inner ℝ (C.heatBathHamiltonianL2 f) f ∧
      inner ℝ (C.heatBathHamiltonianL2 f) f ≤
        (Fintype.card C.base.geometry.Edge : ℝ) * ‖f‖ ^ 2 := by
  have hfInner : inner ℝ C.gibbsVacuumL2 f = 0 :=
    (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff C f).mp hfOrth
  exact
    ⟨continuous_compact_oriented_randomScanDobrushinHamiltonianL2_gap_on_vacuumOrthogonal
        C D f hfInner,
      continuous_compact_oriented_heatBathHamiltonianL2_inner_le_edgeCard_mul_norm_sq
        C D.edgeCard_pos f⟩

end

end MathlibAnalytic
end MGAP4D
