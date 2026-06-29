import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionL2Identification

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Concrete pointwise fluctuation of a real observable under exact Haar
resampling of one physical link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.base.Configuration → ℝ :=
  f - C.singleLinkHeatBathProjection target f

/-- Concrete one-link Haar fluctuation of a strongly measurable observable is
strongly measurable. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (C.singleLinkHeatBathFluctuation target f) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation
  exact hf.sub
    (continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target f hf)

/-- A uniformly bounded observable has one-link Haar fluctuation bounded by
twice the original bound. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M)
    (A : C.base.Configuration) :
    |C.singleLinkHeatBathFluctuation target f A| ≤ 2 * M := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation
  simp only [Pi.sub_apply]
  calc
    |f A - C.singleLinkHeatBathProjection target f A| ≤
        |f A| + |C.singleLinkHeatBathProjection target f A| :=
      abs_sub _ _
    _ ≤ M + M := add_le_add (hM A)
      (continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
        C target f hf M hM0 hM A)
    _ = 2 * M := by ring

/-- On strongly measurable uniformly bounded observables, the abstract `L²`
fluctuation projection is exactly the `L²` class of the concrete Haar-kernel
fluctuation. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_toLp_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M) :
    C.singleLinkHeatBathFluctuationL2 target
        ((continuous_compact_oriented_memLp_two_of_uniform_bound
          C f hf M hM0 hM).toLp f) =
      ((continuous_compact_oriented_memLp_two_of_uniform_bound
        C (C.singleLinkHeatBathFluctuation target f)
        (continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
          C target f hf)
        (2 * M) (mul_nonneg (by norm_num) hM0)
        (continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
          C target f hf M hM0 hM)).toLp
        (C.singleLinkHeatBathFluctuation target f)) := by
  let hfLp : MemLp f 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C f hf M hM0 hM
  let Pf : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathProjection target f
  have hPfStrong : StronglyMeasurable Pf :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target f hf
  have hPfBound : ∀ A, |Pf A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target f hf M hM0 hM
  let hPfLp : MemLp Pf 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C Pf hPfStrong M hM0 hPfBound
  let Qf : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathFluctuation target f
  have hQStrong : StronglyMeasurable Qf :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target f hf
  have hQBound : ∀ A, |Qf A| ≤ 2 * M :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
      C target f hf M hM0 hM
  let hQfLp : MemLp Qf 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C Qf hQStrong (2 * M)
      (mul_nonneg (by norm_num) hM0) hQBound
  have hProjection :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target f hf M hM0 hM
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    hProjection]
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_sub (hfLp.toLp f) (hPfLp.toLp Pf),
      hfLp.coeFn_toLp, hPfLp.coeFn_toLp, hQfLp.coeFn_toLp] with
      A hSubA hfA hPfA hQfA
  rw [hSubA]
  change (hfLp.toLp f) A - (hPfLp.toLp Pf) A =
    (hQfLp.toLp Qf) A
  rw [hfA, hPfA, hQfA]
  rfl

end

end MathlibAnalytic
end MGAP4D
