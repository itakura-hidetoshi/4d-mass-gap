import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathSetIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A strongly measurable uniformly bounded real observable belongs to Gibbs
`L²`. -/
theorem continuous_compact_oriented_memLp_two_of_uniform_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M) :
    MemLp f 2 C.gibbsMeasure := by
  have hConst : MemLp
      (fun _ : C.base.Configuration => M) 2 C.gibbsMeasure :=
    memLp_const M
  apply hConst.of_le hf.aestronglyMeasurable
  filter_upwards [] with A
  simpa [Real.norm_eq_abs, abs_of_nonneg hM0] using hM A

/-- Exact compact Haar conditional expectation preserves every uniform real
absolute-value bound. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M)
    (A : C.base.Configuration) :
    |C.singleLinkHeatBathProjection target f A| ≤ M := by
  have hInt : Integrable f (C.singleLinkHeatBathKernel target A) :=
    continuous_compact_oriented_integrable_singleLinkHeatBathKernel_of_uniform_bound
      C target f hf M hM A
  rw [← continuous_compact_oriented_integral_singleLinkHeatBathKernel_eq_projection
    C target f hf A]
  calc
    |∫ B, f B ∂C.singleLinkHeatBathKernel target A| =
        ‖∫ B, f B ∂C.singleLinkHeatBathKernel target A‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ B, ‖f B‖ ∂C.singleLinkHeatBathKernel target A :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _B, M ∂C.singleLinkHeatBathKernel target A := by
      apply integral_mono_ae hInt.norm (integrable_const M)
      filter_upwards [] with B
      simpa [Real.norm_eq_abs] using hM B
    _ = M := by simp

/-- The pointwise compact Haar heat-bath projection is exactly conditional
expectation onto the off-link sigma-algebra in Gibbs `L²`, for every strongly
measurable uniformly bounded real observable. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_ae_eq_condExpL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M) :
    C.singleLinkHeatBathProjection target f =ᵐ[C.gibbsMeasure]
      (condExpL2 ℝ ℝ
        (compact_oriented_offLinkMeasurableSpace_le C.base target)
        ((continuous_compact_oriented_memLp_two_of_uniform_bound
          C f hf M hM0 hM).toLp f) :
          Lp ℝ 2 C.gibbsMeasure) := by
  let hm := compact_oriented_offLinkMeasurableSpace_le C.base target
  let hfLp : MemLp f 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C f hf M hM0 hM
  let Pf : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathProjection target f
  have hPfStrong :
      StronglyMeasurable[C.base.offLinkMeasurableSpace target] Pf :=
    continuous_compact_oriented_singleLinkHeatBathProjection_offLinkStronglyMeasurable
      C target f hf
  have hPfBound : ∀ A, |Pf A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target f hf M hM0 hM
  let hPfLp : MemLp Pf 2 C.gibbsMeasure := by
    have hConst : MemLp
        (fun _ : C.base.Configuration => M) 2 C.gibbsMeasure :=
      memLp_const M
    apply hConst.of_le hPfStrong.aestronglyMeasurable.mono_ac
    filter_upwards [] with A
    simpa [Real.norm_eq_abs, abs_of_nonneg hM0] using hPfBound A
  let fL2 : Lp ℝ 2 C.gibbsMeasure := hfLp.toLp f
  let pL2 : Lp ℝ 2 C.gibbsMeasure := hPfLp.toLp Pf
  have hpMeas :
      AEStronglyMeasurable[C.base.offLinkMeasurableSpace target]
        pL2 C.gibbsMeasure := by
    exact hPfStrong.aestronglyMeasurable.congr hPfLp.coeFn_toLp.symm
  have hcMeas :
      AEStronglyMeasurable[C.base.offLinkMeasurableSpace target]
        (condExpL2 ℝ ℝ hm fL2 : Lp ℝ 2 C.gibbsMeasure)
        C.gibbsMeasure :=
    lpMeas.aestronglyMeasurable _
  have hLpEq : pL2 =ᵐ[C.gibbsMeasure]
      (condExpL2 ℝ ℝ hm fL2 : Lp ℝ 2 C.gibbsMeasure) := by
    apply Lp.ae_eq_of_forall_setIntegral_eq' ℝ hm pL2
      (condExpL2 ℝ ℝ hm fL2 : Lp ℝ 2 C.gibbsMeasure)
      two_ne_zero ENNReal.coe_ne_top
    · intro s hs hμs
      exact integrableOn_Lp_of_measure_ne_top pL2
        fact_one_le_two_ennreal.elim hμs.ne
    · intro s hs hμs
      exact integrableOn_Lp_of_measure_ne_top
        (condExpL2 ℝ ℝ hm fL2 : Lp ℝ 2 C.gibbsMeasure)
        fact_one_le_two_ennreal.elim hμs.ne
    · intro s hs hμs
      calc
        ∫ A in s, pL2 A ∂C.gibbsMeasure =
            ∫ A in s, Pf A ∂C.gibbsMeasure :=
          setIntegral_congr_ae (hm s hs)
            (ae_restrict_of_ae hPfLp.coeFn_toLp)
        _ = ∫ A in s, f A ∂C.gibbsMeasure :=
          continuous_compact_oriented_setIntegral_singleLinkHeatBathProjection_eq
            C target f hf M hM0 hM s hs
        _ = ∫ A in s, fL2 A ∂C.gibbsMeasure :=
          setIntegral_congr_ae (hm s hs)
            (ae_restrict_of_ae hfLp.coeFn_toLp.symm)
        _ = ∫ A in s,
            (condExpL2 ℝ ℝ hm fL2 : Lp ℝ 2 C.gibbsMeasure) A
            ∂C.gibbsMeasure :=
          (integral_condExpL2_eq hm fL2 hs hμs.ne).symm
    · exact hpMeas
    · exact hcMeas
  exact hPfLp.coeFn_toLp.symm.trans hLpEq

end

end MathlibAnalytic
end MGAP4D
