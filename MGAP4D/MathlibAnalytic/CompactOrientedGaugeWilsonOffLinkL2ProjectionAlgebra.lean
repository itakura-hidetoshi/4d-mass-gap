import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonOffLinkL2Projection
namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
noncomputable section

theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathProjectionL2 target).comp (C.singleLinkHeatBathProjectionL2 target) =
      C.singleLinkHeatBathProjectionL2 target := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply]
  let hm : C.base.offLinkMeasurableSpace target ≤
      (inferInstance : MeasurableSpace C.base.Configuration) :=
    compact_oriented_offLinkMeasurableSpace_le C.base target
  letI : Fact (C.base.offLinkMeasurableSpace target ≤
      (inferInstance : MeasurableSpace C.base.Configuration)) := ⟨hm⟩
  let q : lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target) 2 C.gibbsMeasure :=
    condExpL2 ℝ ℝ hm f
  change ((condExpL2 ℝ ℝ hm (q : Lp ℝ 2 C.gibbsMeasure) :
    lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target) 2 C.gibbsMeasure) :
    Lp ℝ 2 C.gibbsMeasure) = (q : Lp ℝ 2 C.gibbsMeasure)
  have hq : (condExpL2 ℝ ℝ hm (q : Lp ℝ 2 C.gibbsMeasure) :
      lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target) 2 C.gibbsMeasure) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  exact congrArg (fun x : lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target) 2 C.gibbsMeasure =>
    (x : Lp ℝ 2 C.gibbsMeasure)) hq

theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathProjectionL2 target (C.singleLinkHeatBathProjectionL2 target f) =
      C.singleLinkHeatBathProjectionL2 target f := by
  have h := congrArg (fun T : Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure => T f)
    (continuous_compact_oriented_singleLinkHeatBathProjectionL2_idempotent C target)
  simpa using h

noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  ContinuousLinearMap.id ℝ (Lp ℝ 2 C.gibbsMeasure) - C.singleLinkHeatBathProjectionL2 target

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathFluctuationL2 target f = f - C.singleLinkHeatBathProjectionL2 target f := rfl

theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_projection_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathFluctuationL2 target (C.singleLinkHeatBathProjectionL2 target f) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]
  simp

theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathFluctuationL2 target).comp (C.singleLinkHeatBathFluctuationL2 target) =
      C.singleLinkHeatBathFluctuationL2 target := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply,
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply, map_sub,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]
  abel

theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation
    (C : ContinuousCompactOrientedGaugeWilsonSystem) (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathFluctuationL2 target (C.singleLinkHeatBathFluctuationL2 target f) =
      C.singleLinkHeatBathFluctuationL2 target f := by
  have h := congrArg (fun T : Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure => T f)
    (continuous_compact_oriented_singleLinkHeatBathFluctuationL2_idempotent C target)
  simpa using h

end
end MathlibAnalytic
end MGAP4D
