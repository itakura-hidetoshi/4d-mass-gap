import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathBochnerKernel

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Gibbs pairing for real observables of the compact orientation-correct
Wilson system. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.base.Configuration → ℝ) : ℝ :=
  ∫ A, f A * g A ∂C.gibbsMeasure

/-- A strongly measurable uniformly bounded observable is integrable under
every one-link heat-bath transition measure. -/
theorem continuous_compact_oriented_integrable_singleLinkHeatBathKernel_of_uniform_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM : ∀ A, |f A| ≤ M)
    (A : C.base.Configuration) :
    Integrable f (C.singleLinkHeatBathKernel target A) :=
  continuous_compact_oriented_integrable_of_uniform_bound
    (C.singleLinkHeatBathKernel target A) f hf M hM

/-- The exact compact one-link Haar heat-bath projection is symmetric for the
Gibbs pairing on strongly measurable uniformly bounded observables. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_gibbsPairing_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f g : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g)
    (Mf Mg : ℝ)
    (hMf0 : 0 ≤ Mf)
    (hMg0 : 0 ≤ Mg)
    (hMf : ∀ A, |f A| ≤ Mf)
    (hMg : ∀ A, |g A| ≤ Mg) :
    C.gibbsPairingReal (C.singleLinkHeatBathProjection target f) g =
      C.gibbsPairingReal f (C.singleLinkHeatBathProjection target g) := by
  let J := C.singleLinkHeatBathJointMeasure target
  let Phi : C.base.Configuration × C.base.Configuration → ℝ :=
    fun z => f z.2 * g z.1
  have hPhiSM : StronglyMeasurable Phi :=
    (hf.comp_measurable measurable_snd).mul
      (hg.comp_measurable measurable_fst)
  have hPhiBound : ∀ z, |Phi z| ≤ Mf * Mg := by
    intro z
    rw [abs_mul]
    exact mul_le_mul (hMf z.2) (hMg z.1) (abs_nonneg _) hMf0
  have hPhiInt : Integrable Phi J :=
    continuous_compact_oriented_integrable_joint_of_uniform_bound
      C target Phi hPhiSM (Mf * Mg) hPhiBound
  have hSwapSM : StronglyMeasurable (fun z => Phi z.swap) :=
    hPhiSM.comp_measurable measurable_swap
  have hSwapBound : ∀ z, |Phi z.swap| ≤ Mf * Mg := by
    intro z
    exact hPhiBound z.swap
  have hSwapInt : Integrable (fun z => Phi z.swap) J :=
    continuous_compact_oriented_integrable_joint_of_uniform_bound
      C target (fun z => Phi z.swap) hSwapSM (Mf * Mg) hSwapBound
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  calc
    (∫ A, C.singleLinkHeatBathProjection target f A * g A
        ∂C.gibbsMeasure) =
      ∫ A,
        (∫ B, f B ∂C.singleLinkHeatBathKernel target A) * g A
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [continuous_compact_oriented_integral_singleLinkHeatBathKernel_eq_projection
        C target f hf A]
    _ = ∫ A,
        ∫ B, f B * g A ∂C.singleLinkHeatBathKernel target A
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [integral_mul_const]
    _ = ∫ z, Phi z ∂J :=
      (continuous_compact_oriented_integral_singleLinkHeatBathJointMeasure
        C target Phi hPhiInt).symm
    _ = ∫ z, Phi z.swap ∂J :=
      continuous_compact_oriented_integral_singleLinkHeatBathJointMeasure_symm
        C target Phi hPhiSM.aestronglyMeasurable
    _ = ∫ A,
        ∫ B, f A * g B ∂C.singleLinkHeatBathKernel target A
        ∂C.gibbsMeasure := by
      simpa [Phi] using
        (continuous_compact_oriented_integral_singleLinkHeatBathJointMeasure
          C target (fun z => Phi z.swap) hSwapInt)
    _ = ∫ A,
        f A * (∫ B, g B ∂C.singleLinkHeatBathKernel target A)
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [integral_const_mul]
    _ = ∫ A,
        f A * C.singleLinkHeatBathProjection target g A
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [continuous_compact_oriented_integral_singleLinkHeatBathKernel_eq_projection
        C target g hg A]

end

end MathlibAnalytic
end MGAP4D
