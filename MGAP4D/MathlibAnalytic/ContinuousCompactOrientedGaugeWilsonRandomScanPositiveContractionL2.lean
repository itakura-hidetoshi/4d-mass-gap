import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathRandomScanOperatorL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The quadratic form of each exact one-link compact Haar conditional
expectation is the squared norm of its projected component. -/
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

/-- Every exact one-link compact Haar conditional expectation has a
nonnegative quadratic form. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.singleLinkHeatBathProjectionL2 target f) f := by
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_quadraticForm]
  exact sq_nonneg _

/-- The normalized compact Haar random-scan quadratic form is the average of
squared one-link conditional-expectation norms. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.randomScanHeatBathL2 f) f =
      (1 / (Fintype.card C.base.geometry.Edge : ℝ)) *
        ∑ target : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathProjectionL2 target f‖ ^ 2 := by
  classical
  rw [continuous_compact_oriented_randomScanHeatBathL2_apply,
    real_inner_smul_left,
    continuous_compact_oriented_heatBathProjectionSumL2_apply,
    sum_inner]
  refine congrArg
    (fun x : ℝ => (1 / (Fintype.card C.base.geometry.Edge : ℝ)) * x) ?_
  apply Finset.sum_congr rfl
  intro target _htarget
  exact continuous_compact_oriented_singleLinkHeatBathProjectionL2_quadraticForm
    C target f

/-- On a nonempty physical-link set, the normalized random-scan operator is
positive in quadratic-form order. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.randomScanHeatBathL2 f) f := by
  rw [continuous_compact_oriented_randomScanHeatBathL2_quadraticForm]
  have hCard :
      0 < (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  exact mul_nonneg
    (le_of_lt (one_div_pos.mpr hCard))
    (Finset.sum_nonneg fun target _ => sq_nonneg _)

/-- The normalized random-scan operator is bounded above by the identity in
quadratic-form order. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_inner_le_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.randomScanHeatBathL2 f) f ≤ ‖f‖ ^ 2 := by
  have hHamiltonian :=
    continuous_compact_oriented_heatBathHamiltonianL2_nonneg C f
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_eq_edgeCard_mul_randomScanDefect
    C hEdge f] at hHamiltonian
  have hCard :
      0 < (Fintype.card C.base.geometry.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  nlinarith

/-- The normalized compact Haar random-scan quadratic form lies in the closed
unit interval relative to the squared norm. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_quadraticForm_bounds
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.randomScanHeatBathL2 f) f ∧
      inner ℝ (C.randomScanHeatBathL2 f) f ≤ ‖f‖ ^ 2 :=
  ⟨continuous_compact_oriented_randomScanHeatBathL2_nonneg C hEdge f,
    continuous_compact_oriented_randomScanHeatBathL2_inner_le_norm_sq C hEdge f⟩

end

end MathlibAnalytic
end MGAP4D
