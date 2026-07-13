import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ContinuousCompactRandomScanL2Structure

/-!
Operator-theoretic structure of the genuine compact-Haar random-scan heat-bath
operator. This file proves from exact conditional-expectation projections that
random scan is positive and self-adjoint, fixes the Gibbs vacuum, and is exactly
`I - |E|⁻¹ H_HB`.
-/

/-- Every one-link compact-Haar conditional expectation has quadratic form equal
to the squared norm of the projected vector. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.singleLinkHeatBathProjectionL2 target f) f =
      ‖C.singleLinkHeatBathProjectionL2 target f‖ ^ 2 := by
  calc
    inner ℝ (C.singleLinkHeatBathProjectionL2 target f) f =
        inner ℝ
          (C.singleLinkHeatBathProjectionL2 target
            (C.singleLinkHeatBathProjectionL2 target f)) f := by
      rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]
    _ = inner ℝ
        (C.singleLinkHeatBathProjectionL2 target f)
        (C.singleLinkHeatBathProjectionL2 target f) :=
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm
        C target (C.singleLinkHeatBathProjectionL2 target f) f
    _ = ‖C.singleLinkHeatBathProjectionL2 target f‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- A one-link compact-Haar conditional expectation is positive in quadratic
form. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.singleLinkHeatBathProjectionL2 target f) f := by
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_quadraticForm]
  exact sq_nonneg _

/-- The normalized compact-Haar random-scan operator is the identity minus the
edge-cardinality-normalized native heat-bath Hamiltonian. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.randomScanHeatBathL2 f =
      f - (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ •
        C.heatBathHamiltonianL2 f := by
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hEdge
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hHamiltonian :=
    continuous_compact_oriented_heatBathHamiltonianL2_eq_card_smul_sub_projectionSum
      C f
  have hProjection :
      C.heatBathProjectionSumL2 f = n • f - C.heatBathHamiltonianL2 f := by
    dsimp [n]
    rw [hHamiltonian]
    abel
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply, hProjection,
    smul_sub, smul_smul]
  simp only [one_div]
  change (n⁻¹ * n) • f - n⁻¹ • C.heatBathHamiltonianL2 f =
    f - n⁻¹ • C.heatBathHamiltonianL2 f
  rw [inv_mul_cancel₀ hn0, one_smul]

/-- The exact compact-Haar random-scan operator is self-adjoint in the Gibbs
real `L²` pairing. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f g : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.randomScanHeatBathL2 f) g =
      inner ℝ f (C.randomScanHeatBathL2 g) := by
  rw [continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
      C hEdge f,
    continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
      C hEdge g,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right,
    continuous_compact_oriented_heatBathHamiltonianL2_inner_symm]

/-- Exact quadratic-form identity relating the random-scan operator and the
native heat-bath Hamiltonian. -/
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

/-- The random-scan quadratic form is nonnegative because it is the normalized
sum of positive one-link conditional-expectation quadratic forms. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.randomScanHeatBathL2 f) f := by
  have hCard :
      0 ≤ (1 / (Fintype.card C.base.geometry.Edge : ℝ)) := by
    positivity
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply,
    real_inner_smul_left,
    continuous_compact_oriented_heatBathProjectionSumL2_apply,
    sum_inner]
  apply mul_nonneg hCard
  exact Finset.sum_nonneg fun target _ =>
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_nonneg
      C target f

/-- The random-scan quadratic form is bounded above by the squared `L²` norm. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_quadraticForm_le_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.randomScanHeatBathL2 f) f ≤ ‖f‖ ^ 2 := by
  rw [continuous_compact_oriented_randomScanHeatBathL2_quadraticForm C hEdge f]
  have hInv :
      0 ≤ (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ := by
    positivity
  have hHamiltonian :=
    continuous_compact_oriented_heatBathHamiltonianL2_nonneg C f
  nlinarith

/-- The exact compact-Haar random-scan operator fixes the normalized Gibbs
vacuum. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    C.randomScanHeatBathL2 C.gibbsVacuumL2 = C.gibbsVacuumL2 := by
  rw [continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
      C hEdge C.gibbsVacuumL2,
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
    smul_zero, sub_zero]

/-- Random scan preserves the Gibbs-vacuum coefficient. -/
theorem continuous_compact_oriented_inner_vacuum_randomScanHeatBathL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ C.gibbsVacuumL2 (C.randomScanHeatBathL2 f) =
      inner ℝ C.gibbsVacuumL2 f := by
  rw [← continuous_compact_oriented_randomScanHeatBathL2_inner_symm
      C hEdge C.gibbsVacuumL2 f,
    continuous_compact_oriented_randomScanHeatBathL2_vacuum C hEdge]

/-- The random-scan operator commutes with orthogonal centering away from the
normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_vacuumCentered
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.randomScanHeatBathL2 (C.vacuumCenteredL2 f) =
      C.vacuumCenteredL2 (C.randomScanHeatBathL2 f) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [map_sub, map_smul,
    continuous_compact_oriented_randomScanHeatBathL2_vacuum C hEdge,
    continuous_compact_oriented_inner_vacuum_randomScanHeatBathL2 C hEdge f]

/-- The centered random-scan Rayleigh estimate with rate `1 - gap / |E|` is
exactly equivalent to the native heat-bath Poincaré inequality with gap `gap`.
No finite-dimensional eigenbasis is used. -/
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
    have hIdentity :=
      continuous_compact_oriented_randomScanHeatBathL2_quadraticForm C hEdge q
    have hCenteredHamiltonian :=
      continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered_quadraticForm
        C f
    change gap * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f
    rw [← hCenteredHamiltonian]
    change gap * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 q) q
    rw [hIdentity] at hRandom
    have hCard :
        (0 : ℝ) < (Fintype.card C.base.geometry.Edge : ℝ) :=
      Nat.cast_pos.mpr hEdge
    have hInvPos :
        0 < (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ :=
      inv_pos.mpr hCard
    by_contra hGap
    have hGapLt :
        inner ℝ (C.heatBathHamiltonianL2 q) q <
          gap * ‖q‖ ^ 2 :=
      lt_of_not_ge hGap
    have hScaled :
        (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
            inner ℝ (C.heatBathHamiltonianL2 q) q <
          (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
            (gap * ‖q‖ ^ 2) :=
      mul_lt_mul_of_pos_left hGapLt hInvPos
    have hStrict :
        (1 - gap / (Fintype.card C.base.geometry.Edge : ℝ)) *
            ‖q‖ ^ 2 <
          ‖q‖ ^ 2 -
            (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
              inner ℝ (C.heatBathHamiltonianL2 q) q := by
      calc
        (1 - gap / (Fintype.card C.base.geometry.Edge : ℝ)) *
              ‖q‖ ^ 2 =
            ‖q‖ ^ 2 -
              (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
                (gap * ‖q‖ ^ 2) := by
          rw [div_eq_mul_inv]
          ring
        _ < ‖q‖ ^ 2 -
              (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
                inner ℝ (C.heatBathHamiltonianL2 q) q :=
          sub_lt_sub_left hScaled (‖q‖ ^ 2)
    exact (not_lt_of_ge hRandom) hStrict
  · intro hPoincare f
    let q : Lp ℝ 2 C.gibbsMeasure := C.vacuumCenteredL2 f
    have hGap := hPoincare f
    have hIdentity :=
      continuous_compact_oriented_randomScanHeatBathL2_quadraticForm C hEdge q
    have hCenteredHamiltonian :=
      continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered_quadraticForm
        C f
    change
      inner ℝ (C.randomScanHeatBathL2 q) q ≤
        (1 - gap / (Fintype.card C.base.geometry.Edge : ℝ)) * ‖q‖ ^ 2
    rw [hIdentity]
    rw [← hCenteredHamiltonian] at hGap
    change gap * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 q) q at hGap
    have hCard :
        (0 : ℝ) < (Fintype.card C.base.geometry.Edge : ℝ) :=
      Nat.cast_pos.mpr hEdge
    have hInvNonneg :
        0 ≤ (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ :=
      (inv_pos.mpr hCard).le
    have hScaled :
        (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
            (gap * ‖q‖ ^ 2) ≤
          (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
            inner ℝ (C.heatBathHamiltonianL2 q) q :=
      mul_le_mul_of_nonneg_left hGap hInvNonneg
    calc
      ‖q‖ ^ 2 -
            (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
              inner ℝ (C.heatBathHamiltonianL2 q) q ≤
          ‖q‖ ^ 2 -
            (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
              (gap * ‖q‖ ^ 2) :=
        sub_le_sub_left hScaled (‖q‖ ^ 2)
      _ =
          (1 - gap / (Fintype.card C.base.geometry.Edge : ℝ)) *
            ‖q‖ ^ 2 := by
        rw [div_eq_mul_inv]
        ring

end ContinuousCompactRandomScanL2Structure

end

end MathlibAnalytic
end MGAP4D
