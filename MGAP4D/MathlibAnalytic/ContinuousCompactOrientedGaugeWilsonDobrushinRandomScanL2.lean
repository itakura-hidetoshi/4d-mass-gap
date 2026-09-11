import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinPoincareL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Normalized random-scan average of the exact one-link compact Haar
conditional-expectation projections. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  (1 / (Fintype.card C.base.geometry.Edge : ℝ)) •
    C.heatBathProjectionSumL2

@[simp] theorem continuous_compact_oriented_randomScanHeatBathL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.randomScanHeatBathL2 f =
      (1 / (Fintype.card C.base.geometry.Edge : ℝ)) •
        C.heatBathProjectionSumL2 f :=
  rfl

/-- Standard normalized random-scan rate associated with a Dobrushin
coefficient. -/
def continuousCompactOrientedDobrushinRandomScanRate
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (coefficient : ℝ) : ℝ :=
  1 - continuousCompactOrientedDobrushinHeatBathGap coefficient /
    (Fintype.card C.base.geometry.Edge : ℝ)

/-- For a nonempty physical-link set, the normalized random-scan rate lies
below one whenever the Dobrushin coefficient is strictly below one. -/
theorem continuous_compact_oriented_dobrushinRandomScanRate_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (coefficient : ℝ)
    (hCoefficient : coefficient < 1)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    continuousCompactOrientedDobrushinRandomScanRate C coefficient < 1 := by
  have hCard : (0 : ℝ) < (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hGap :
      0 < continuousCompactOrientedDobrushinHeatBathGap coefficient := by
    unfold continuousCompactOrientedDobrushinHeatBathGap
    exact sub_pos.mpr hCoefficient
  unfold continuousCompactOrientedDobrushinRandomScanRate
  have hDiv :
      0 < continuousCompactOrientedDobrushinHeatBathGap coefficient /
        (Fintype.card C.base.geometry.Edge : ℝ) :=
    div_pos hGap hCard
  linarith

/-- Edge-cardinality normalization recovers the unnormalized heat-bath gap. -/
theorem continuous_compact_oriented_edgeCard_mul_one_sub_dobrushinRandomScanRate
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (coefficient : ℝ)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    (Fintype.card C.base.geometry.Edge : ℝ) *
        (1 - continuousCompactOrientedDobrushinRandomScanRate C coefficient) =
      continuousCompactOrientedDobrushinHeatBathGap coefficient := by
  have hCard : (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold continuousCompactOrientedDobrushinRandomScanRate
  field_simp [hCard]
  ring

/-- The projection-sum quadratic form is the edge-cardinality multiple of the
normalized random-scan quadratic form. -/
theorem continuous_compact_oriented_projectionSum_inner_eq_edgeCard_mul_randomScan_inner
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathProjectionSumL2 f) f =
      (Fintype.card C.base.geometry.Edge : ℝ) *
        inner ℝ (C.randomScanHeatBathL2 f) f := by
  have hCard : (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply,
    real_inner_smul_left]
  field_simp [hCard]

/-- Random-scan form of the compact Dobrushin analytic certificate.  This is
the direct compact-group analogue of the finite Wilson centered Rayleigh
certificate, now on the genuine Gibbs `L²` Hilbert space. -/
structure
    ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate
    (C : ContinuousCompactOrientedGaugeWilsonSystem) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  coefficient_lt_one : coefficient < 1
  edgeCard_pos : 0 < Fintype.card C.base.geometry.Edge
  centered_randomScan_rayleigh_le :
    ∀ f : Lp ℝ 2 C.gibbsMeasure,
      inner ℝ
          (C.randomScanHeatBathL2 (C.vacuumCenteredL2 f))
          (C.vacuumCenteredL2 f) ≤
        continuousCompactOrientedDobrushinRandomScanRate C coefficient *
          ‖C.vacuumCenteredL2 f‖ ^ 2

/-- A centered random-scan contraction canonically produces the unnormalized
projection-sum Rayleigh certificate used by the compact Poincaré theorem. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate.toProjectionSumCertificate
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C := by
  refine
    { coefficient := D.coefficient
      coefficient_nonneg := D.coefficient_nonneg
      coefficient_lt_one := D.coefficient_lt_one
      centered_projectionSum_rayleigh_le := ?_ }
  intro f
  let q : Lp ℝ 2 C.gibbsMeasure := C.vacuumCenteredL2 f
  have hRandom := D.centered_randomScan_rayleigh_le f
  have hScale :=
    continuous_compact_oriented_projectionSum_inner_eq_edgeCard_mul_randomScan_inner
      C D.edgeCard_pos q
  have hCardNonneg :
      0 ≤ (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_nonneg _
  have hRate :=
    continuous_compact_oriented_edgeCard_mul_one_sub_dobrushinRandomScanRate
      C D.coefficient D.edgeCard_pos
  change
    inner ℝ (C.heatBathProjectionSumL2 q) q ≤
      ((Fintype.card C.base.geometry.Edge : ℝ) -
        continuousCompactOrientedDobrushinHeatBathGap D.coefficient) *
          ‖q‖ ^ 2
  rw [hScale]
  calc
    (Fintype.card C.base.geometry.Edge : ℝ) *
        inner ℝ (C.randomScanHeatBathL2 q) q ≤
      (Fintype.card C.base.geometry.Edge : ℝ) *
        (continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
          ‖q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hRandom hCardNonneg
    _ = ((Fintype.card C.base.geometry.Edge : ℝ) -
        continuousCompactOrientedDobrushinHeatBathGap D.coefficient) *
          ‖q‖ ^ 2 := by
      have hRateRearranged :
          (Fintype.card C.base.geometry.Edge : ℝ) *
              continuousCompactOrientedDobrushinRandomScanRate C D.coefficient =
            (Fintype.card C.base.geometry.Edge : ℝ) -
              continuousCompactOrientedDobrushinHeatBathGap D.coefficient := by
        nlinarith
      rw [← mul_assoc, hRateRearranged]

/-- A strict compact random-scan Dobrushin contraction yields the native
heat-bath Poincaré inequality with gap `1 - alpha`. -/
theorem continuous_compact_oriented_randomScanDobrushinHeatBathPoincareL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    C.HeatBathPoincareL2
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :=
  continuous_compact_oriented_dobrushinHeatBathPoincareL2 C
    D.toProjectionSumCertificate

/-- The random-scan Dobrushin certificate gives the explicit native
Hamiltonian gap on the Gibbs-vacuum orthogonal sector. -/
theorem continuous_compact_oriented_randomScanDobrushinHamiltonianL2_gap_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_dobrushinHamiltonianL2_gap_on_vacuumOrthogonal
    C D.toProjectionSumCertificate f hf

/-- Under a strict compact random-scan Dobrushin certificate, the zero-energy
space is exactly the normalized Gibbs-vacuum line. -/
theorem continuous_compact_oriented_randomScanDobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 :=
  continuous_compact_oriented_dobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    C D.toProjectionSumCertificate f

end

end MathlibAnalytic
end MGAP4D
