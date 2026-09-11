import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The finite sum of exact one-link compact Haar conditional expectations is
self-adjoint in the Gibbs `L²` pairing. -/
theorem continuous_compact_oriented_heatBathProjectionSumL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathProjectionSumL2 f) g =
      inner ℝ f (C.heatBathProjectionSumL2 g) := by
  classical
  rw [continuous_compact_oriented_heatBathProjectionSumL2_apply,
    continuous_compact_oriented_heatBathProjectionSumL2_apply,
    sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro target _htarget
  exact
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm
      C target f g

/-- The projection sum sends the normalized Gibbs vacuum to the edge-cardinality
multiple of that vacuum. -/
theorem continuous_compact_oriented_heatBathProjectionSumL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.heatBathProjectionSumL2 C.gibbsVacuumL2 =
      (Fintype.card C.base.geometry.Edge : ℝ) • C.gibbsVacuumL2 := by
  classical
  rw [continuous_compact_oriented_heatBathProjectionSumL2_apply]
  simp_rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_vacuum]
  simp only [Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℝ
    (Fintype.card C.base.geometry.Edge) C.gibbsVacuumL2).symm

/-- The normalized compact Haar random-scan operator is self-adjoint. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.randomScanHeatBathL2 f) g =
      inner ℝ f (C.randomScanHeatBathL2 g) := by
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply,
    continuous_compact_oriented_randomScanHeatBathL2_apply,
    real_inner_smul_left, real_inner_smul_right,
    continuous_compact_oriented_heatBathProjectionSumL2_inner_symm]

/-- On a nonempty physical-link set, normalized random scan fixes the Gibbs
vacuum exactly. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    C.randomScanHeatBathL2 C.gibbsVacuumL2 = C.gibbsVacuumL2 := by
  have hCard : (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply,
    continuous_compact_oriented_heatBathProjectionSumL2_vacuum,
    smul_smul]
  field_simp [hCard]
  exact one_smul ℝ C.gibbsVacuumL2

/-- The native unnormalized compact heat-bath Hamiltonian is the edge-cardinality
multiple of the normalized random-scan defect `I - R`. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_eq_edgeCard_smul_randomScanDefect
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f =
      (Fintype.card C.base.geometry.Edge : ℝ) •
        (f - C.randomScanHeatBathL2 f) := by
  have hCard : (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  rw [continuous_compact_oriented_heatBathHamiltonianL2_eq_card_smul_sub_projectionSum,
    smul_sub, continuous_compact_oriented_randomScanHeatBathL2_apply,
    smul_smul]
  congr 1
  field_simp [hCard]
  exact (one_smul ℝ (C.heatBathProjectionSumL2 f)).symm

/-- Quadratic-form version of `H = |E| (I - R)`. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_eq_edgeCard_mul_randomScanDefect
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f =
      (Fintype.card C.base.geometry.Edge : ℝ) *
        (‖f‖ ^ 2 - inner ℝ (C.randomScanHeatBathL2 f) f) := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_eq_edgeCard_smul_randomScanDefect
      C hEdge f,
    real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]

/-- A random-scan Rayleigh bound with rate `rho` immediately yields the
unnormalized native Hamiltonian lower bound `|E| (1-rho)`. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_gap_of_randomScan_rayleigh
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (rho : ℝ)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hRayleigh :
      inner ℝ (C.randomScanHeatBathL2 f) f ≤ rho * ‖f‖ ^ 2) :
    (Fintype.card C.base.geometry.Edge : ℝ) * (1 - rho) * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_eq_edgeCard_mul_randomScanDefect
    C hEdge f]
  have hCardNonneg :
      0 ≤ (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_nonneg _
  nlinarith [sq_nonneg ‖f‖]

end

end MathlibAnalytic
end MGAP4D
