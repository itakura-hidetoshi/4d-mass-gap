import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionL2Identification
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathHamiltonianL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Concrete pointwise fluctuation of a real observable under exact Haar
resampling of one physical link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationCurrent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.base.Configuration → ℝ :=
  f - C.singleLinkHeatBathProjection target f

/-- Concrete one-link Haar fluctuation of a strongly measurable observable is
strongly measurable. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (C.singleLinkHeatBathFluctuationCurrent target f) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationCurrent
  exact hf.sub
    (continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target f hf)

/-- A uniformly bounded observable has one-link Haar fluctuation bounded by
twice the original bound. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M)
    (A : C.base.Configuration) :
    |C.singleLinkHeatBathFluctuationCurrent target f A| ≤ 2 * M := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationCurrent
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
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2Current_toLp_eq
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
        C (C.singleLinkHeatBathFluctuationCurrent target f)
        (continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_stronglyMeasurable
          C target f hf)
        (2 * M) (mul_nonneg (by norm_num) hM0)
        (continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_abs_le
          C target f hf M hM0 hM)).toLp
        (C.singleLinkHeatBathFluctuationCurrent target f)) := by
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
    C.singleLinkHeatBathFluctuationCurrent target f
  have hQStrong : StronglyMeasurable Qf :=
    continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_stronglyMeasurable
      C target f hf
  have hQBound : ∀ A, |Qf A| ≤ 2 * M :=
    continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_abs_le
      C target f hf M hM0 hM
  let hQfLp : MemLp Qf 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C Qf hQStrong (2 * M)
      (mul_nonneg (by norm_num) hM0) hQBound
  have hProjection :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target f hf M hM0 hM
  apply Lp.ext
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    hProjection]
  filter_upwards
    [hfLp.coeFn_toLp, hPfLp.coeFn_toLp, hQfLp.coeFn_toLp] with A hfA hPfA hQfA
  change
    ((hfLp.toLp f : C.base.Configuration → ℝ) A -
      (hPfLp.toLp Pf : C.base.Configuration → ℝ) A) =
      (hQfLp.toLp Qf : C.base.Configuration → ℝ) A
  rw [hfA, hPfA, hQfA]
  rfl

/-- For a strongly measurable uniformly bounded observable, the abstract
compact heat-bath Hamiltonian quadratic form is the finite sum of the squared
`L²` norms of its concrete one-link Haar fluctuations. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_boundedObservableCurrent_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M) :
    inner ℝ
        (C.heatBathHamiltonianL2
          ((continuous_compact_oriented_memLp_two_of_uniform_bound
            C f hf M hM0 hM).toLp f))
        ((continuous_compact_oriented_memLp_two_of_uniform_bound
          C f hf M hM0 hM).toLp f) =
      ∑ target : C.base.geometry.Edge,
        ‖((continuous_compact_oriented_memLp_two_of_uniform_bound
          C (C.singleLinkHeatBathFluctuationCurrent target f)
          (continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_stronglyMeasurable
            C target f hf)
          (2 * M) (mul_nonneg (by norm_num) hM0)
          (continuous_compact_oriented_singleLinkHeatBathFluctuationCurrent_abs_le
            C target f hf M hM0 hM)).toLp
          (C.singleLinkHeatBathFluctuationCurrent target f))‖ ^ 2 := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
  apply Finset.sum_congr rfl
  intro target _htarget
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2Current_toLp_eq
    C target f hf M hM0 hM]

end

end MathlibAnalytic
end MGAP4D
