import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHaarGibbsL2Density

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct

noncomputable section

/-- The finite Wilson product Haar law is also absolutely continuous with
respect to the strictly positive Gibbs tilt. -/
theorem continuous_compact_oriented_configurationHaarMeasure_absolutelyContinuous_gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.base.configurationHaarMeasure ≪ C.gibbsMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  exact absolutelyContinuous_tilted
    (continuous_compact_oriented_boltzmannIntegrable C)

/-- An almost-everywhere identity for Haar representatives remains valid under
the finite Wilson Gibbs law. -/
theorem continuous_compact_oriented_ae_haar_to_gibbs
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {p q : C.base.Configuration → Prop}
    (h : ∀ᶠ A ∂C.base.configurationHaarMeasure, p A ↔ q A) :
    ∀ᶠ A ∂C.gibbsMeasure, p A ↔ q A :=
  h.filter_mono
    (Measure.ae_le_iff_absolutelyContinuous.mpr
      (continuous_compact_oriented_gibbsMeasure_absolutelyContinuous C))

/-- An almost-everywhere identity for Gibbs representatives remains valid
under product Haar because the Wilson density is strictly positive. -/
theorem continuous_compact_oriented_ae_gibbs_to_haar
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {p q : C.base.Configuration → Prop}
    (h : ∀ᶠ A ∂C.gibbsMeasure, p A ↔ q A) :
    ∀ᶠ A ∂C.base.configurationHaarMeasure, p A ↔ q A :=
  h.filter_mono
    (Measure.ae_le_iff_absolutelyContinuous.mpr
      (continuous_compact_oriented_configurationHaarMeasure_absolutelyContinuous_gibbsMeasure C))

/-- Inverse-square-root density transport as an actual Gibbs `L²` vector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.configurationHaarL2) : Lp ℝ 2 C.gibbsMeasure :=
  (continuous_compact_oriented_haarToGibbsL2Function_memLp C f).toLp
    (C.haarToGibbsL2Function f)

/-- The Gibbs representative of inverse-square-root density transport is the
expected pointwise weighted Haar representative. -/
theorem continuous_compact_oriented_haarToGibbsL2_coeFn
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.configurationHaarL2) :
    C.haarToGibbsL2 f =ᵐ[C.gibbsMeasure]
      C.haarToGibbsL2Function f :=
  MemLp.coeFn_toLp
    (continuous_compact_oriented_haarToGibbsL2Function_memLp C f)

/-- Inverse-square-root density transport preserves addition. -/
theorem continuous_compact_oriented_haarToGibbsL2_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.configurationHaarL2) :
    C.haarToGibbsL2 (f + g) =
      C.haarToGibbsL2 f + C.haarToGibbsL2 g := by
  apply Lp.ext
  have hsource := continuous_compact_oriented_ae_haar_to_gibbs C
    (Lp.coeFn_add f g)
  filter_upwards
    [continuous_compact_oriented_haarToGibbsL2_coeFn C (f + g),
      continuous_compact_oriented_haarToGibbsL2_coeFn C f,
      continuous_compact_oriented_haarToGibbsL2_coeFn C g,
      Lp.coeFn_add (C.haarToGibbsL2 f) (C.haarToGibbsL2 g),
      hsource] with A hsum hf hg htarget hsrc
  rw [hsum, htarget, hf, hg]
  simp only [ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Function,
    Pi.add_apply, hsrc]
  ring

/-- Inverse-square-root density transport preserves real scalar
multiplication. -/
theorem continuous_compact_oriented_haarToGibbsL2_smul
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (r : ℝ)
    (f : C.configurationHaarL2) :
    C.haarToGibbsL2 (r • f) = r • C.haarToGibbsL2 f := by
  apply Lp.ext
  have hsource := continuous_compact_oriented_ae_haar_to_gibbs C
    (Lp.coeFn_smul r f)
  filter_upwards
    [continuous_compact_oriented_haarToGibbsL2_coeFn C (r • f),
      continuous_compact_oriented_haarToGibbsL2_coeFn C f,
      Lp.coeFn_smul r (C.haarToGibbsL2 f),
      hsource] with A hsmul hf htarget hsrc
  rw [hsmul, htarget, hf]
  simp only [ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Function,
    Pi.smul_apply, hsrc, smul_eq_mul]
  ring

/-- Inverse-square-root Wilson density transport as a real linear map. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2LinearMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.configurationHaarL2 →ₗ[ℝ] Lp ℝ 2 C.gibbsMeasure where
  toFun := C.haarToGibbsL2
  map_add' := continuous_compact_oriented_haarToGibbsL2_add C
  map_smul' := continuous_compact_oriented_haarToGibbsL2_smul C

/-- The inverse-square-root density transport preserves the real `L²` inner
product exactly. -/
theorem continuous_compact_oriented_haarToGibbsL2_inner
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.configurationHaarL2) :
    inner ℝ (C.haarToGibbsL2 f) (C.haarToGibbsL2 g) =
      inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [integral_tilted]
  have hf := continuous_compact_oriented_ae_gibbs_to_haar C
    (continuous_compact_oriented_haarToGibbsL2_coeFn C f)
  have hg := continuous_compact_oriented_ae_gibbs_to_haar C
    (continuous_compact_oriented_haarToGibbsL2_coeFn C g)
  apply integral_congr_ae
  filter_upwards [hf, hg] with A hfA hgA
  rw [hfA, hgA]
  simp only [ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Function,
    smul_eq_mul]
  change
    (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) *
        ((C.haarToGibbsL2Weight A * f A) *
          (C.haarToGibbsL2Weight A * g A)) =
      f A * g A
  calc
    (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) *
        ((C.haarToGibbsL2Weight A * f A) *
          (C.haarToGibbsL2Weight A * g A)) =
      ((Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) *
        C.haarToGibbsL2Weight A ^ 2) * (f A * g A) := by ring
    _ = f A * g A := by
      rw [continuous_compact_oriented_normalizedDensity_mul_haarToGibbsL2Weight_sq]
      simp

/-- Inverse-square-root Wilson density transport preserves the `L²` norm. -/
theorem continuous_compact_oriented_haarToGibbsL2_norm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.configurationHaarL2) :
    ‖C.haarToGibbsL2 f‖ = ‖f‖ := by
  have hinner := continuous_compact_oriented_haarToGibbsL2_inner C f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (C.haarToGibbsL2 f), norm_nonneg f]

/-- The actual finite Wilson inverse-square-root density change is a real
linear isometric embedding from product Haar `L²` into Gibbs `L²`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Isometry
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.configurationHaarL2 →ₗᵢ[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  LinearIsometry.mk C.haarToGibbsL2LinearMap
    (continuous_compact_oriented_haarToGibbsL2_norm C)

end

end MathlibAnalytic
end MGAP4D
