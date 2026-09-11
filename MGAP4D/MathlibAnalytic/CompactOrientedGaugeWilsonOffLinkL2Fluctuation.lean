import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonOffLinkL2ProjectionAlgebra

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The compact one-link `L²` fluctuation projection is self-adjoint. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f g : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.singleLinkHeatBathFluctuationL2 target f) g =
      inner ℝ f (C.singleLinkHeatBathFluctuationL2 target g) := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    inner_sub_left, inner_sub_right,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm]

/-- The local compact-group heat-bath quadratic form is the squared norm of
the local `L²` fluctuation. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.singleLinkHeatBathFluctuationL2 target f) f =
      ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 := by
  calc
    inner ℝ (C.singleLinkHeatBathFluctuationL2 target f) f =
        inner ℝ f (C.singleLinkHeatBathFluctuationL2 target f) :=
      real_inner_comm _ _
    _ = inner ℝ
        (C.singleLinkHeatBathFluctuationL2 target f)
        (C.singleLinkHeatBathFluctuationL2 target f) := by
      rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_inner_symm,
        continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation]
    _ = ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Every local compact-group heat-bath fluctuation projection has a
nonnegative quadratic form. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.singleLinkHeatBathFluctuationL2 target f) f := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_quadraticForm]
  exact sq_nonneg _

end

end MathlibAnalytic
end MGAP4D
