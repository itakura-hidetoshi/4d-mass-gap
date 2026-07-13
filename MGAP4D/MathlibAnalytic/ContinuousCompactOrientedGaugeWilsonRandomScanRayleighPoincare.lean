import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace ContinuousCompactRandomScanRayleighPoincare

/-- Elementary positive-cardinality algebra behind the normalized random-scan
Rayleigh estimate and the unnormalized heat-bath coercivity estimate. -/
theorem normalized_defect_le_iff
    (card gap normSq energy : ℝ)
    (hcard : 0 < card) :
    normSq - card⁻¹ * energy ≤ (1 - gap / card) * normSq ↔
      gap * normSq ≤ energy := by
  have hcard0 : card ≠ 0 := ne_of_gt hcard
  have hIdentity :
      card *
          ((normSq - card⁻¹ * energy) -
            ((1 - gap / card) * normSq)) =
        gap * normSq - energy := by
    field_simp [hcard0]
    ring
  constructor
  · intro h
    have hdiff :
        (normSq - card⁻¹ * energy) -
            ((1 - gap / card) * normSq) ≤ 0 :=
      sub_nonpos.mpr h
    have hscaled :
        card *
            ((normSq - card⁻¹ * energy) -
              ((1 - gap / card) * normSq)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcard.le hdiff
    rw [hIdentity] at hscaled
    exact sub_nonpos.mp hscaled
  · intro h
    have hscaled : gap * normSq - energy ≤ 0 := sub_nonpos.mpr h
    rw [← hIdentity] at hscaled
    have hinv : 0 ≤ card⁻¹ := (inv_pos.mpr hcard).le
    have hunscaled := mul_nonpos_of_nonneg_of_nonpos hinv hscaled
    rw [← mul_assoc, inv_mul_cancel₀ hcard0, one_mul] at hunscaled
    exact sub_nonpos.mp hunscaled

/-- On the genuine compact-Haar Gibbs `L²` space, normalized random scan is the
identity minus the edge-cardinality-normalized native heat-bath Hamiltonian. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.randomScanHeatBathL2 f =
      f - (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ •
        C.heatBathHamiltonianL2 f := by
  have hcard :
      (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply]
  rw [continuous_compact_oriented_heatBathHamiltonianL2_eq_card_smul_sub_projectionSum]
  rw [smul_sub, smul_smul, one_div, inv_mul_cancel₀ hcard, one_smul]
  abel

/-- Exact quadratic-form identity between normalized random scan and the native
compact-Haar heat-bath Hamiltonian. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.randomScanHeatBathL2 f) f =
      ‖f‖ ^ 2 -
        (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
          inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
      C hEdge f,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The centered random-scan Rayleigh estimate with rate
`1 - gap / |Edge|` is exactly equivalent to the native compact-Haar heat-bath
Poincaré inequality with gap `gap`.  The proof uses only the exact operator
identity and positive edge cardinality, not a finite-dimensional eigenbasis. -/
theorem continuous_compact_oriented_randomScanRayleigh_iff_heatBathPoincareL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (gap : ℝ) :
    (∀ f : Lp ℝ 2 C.gibbsMeasure,
      inner ℝ
          (C.randomScanHeatBathL2 (C.vacuumCenteredL2 f))
          (C.vacuumCenteredL2 f) ≤
        (1 - gap / (Fintype.card C.base.geometry.Edge : ℝ)) *
          ‖C.vacuumCenteredL2 f‖ ^ 2) ↔
      C.HeatBathPoincareL2 gap := by
  constructor
  · intro hRayleigh f
    let q : Lp ℝ 2 C.gibbsMeasure := C.vacuumCenteredL2 f
    have hRandom := hRayleigh f
    rw [continuous_compact_oriented_randomScanHeatBathL2_quadraticForm
      C hEdge q] at hRandom
    have hAlgebra :=
      (normalized_defect_le_iff
        (Fintype.card C.base.geometry.Edge : ℝ)
        gap (‖q‖ ^ 2)
        (inner ℝ (C.heatBathHamiltonianL2 q) q)
        (Nat.cast_pos.mpr hEdge)).mp hRandom
    change gap * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f
    rw [← continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered_quadraticForm]
    exact hAlgebra
  · intro hPoincare f
    let q : Lp ℝ 2 C.gibbsMeasure := C.vacuumCenteredL2 f
    have hGap := hPoincare f
    rw [← continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered_quadraticForm]
      at hGap
    change gap * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 q) q at hGap
    rw [continuous_compact_oriented_randomScanHeatBathL2_quadraticForm
      C hEdge q]
    exact
      (normalized_defect_le_iff
        (Fintype.card C.base.geometry.Edge : ℝ)
        gap (‖q‖ ^ 2)
        (inner ℝ (C.heatBathHamiltonianL2 q) q)
        (Nat.cast_pos.mpr hEdge)).mpr hGap

end ContinuousCompactRandomScanRayleighPoincare

end

end MathlibAnalytic
end MGAP4D
