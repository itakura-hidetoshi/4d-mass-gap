import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberConditionalLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathVariationInfluence
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceDistinctFiberOffFiberVariationPropagationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberOffFiberVariationPropagationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberOffFiberVariationPropagationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberOffFiberVariationPropagationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberOffFiberVariationPropagationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberOffFiberVariationPropagationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The explicit off-fiber coefficient obtained from the normalized literal C5
conditional law is nonnegative for physical `beta ≥ 0`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
  have hExp : 1 ≤ Real.exp (32 * beta) := by
    apply Real.one_le_exp.mpr
    nlinarith
  have hSq : 1 ≤ (Real.exp (32 * beta)) ^ 2 := by
    nlinarith [Real.exp_pos (32 * beta)]
  exact mul_nonneg (by norm_num)
    (div_nonneg (sub_nonneg.mpr hSq) (by positivity))

/-- Scaling the normalized bounded-test estimate from unit oscillation to an
arbitrary declared fiber variation.  This is the literal C5 off-fiber analogue
of the already-proved cross-boundary variation scaling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fiberVariation_influence_update_distinct_background
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : backgroundFiber ≠ fiber)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (hFiberVariation :
      ∀ u v : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |phi u - phi v| ≤ magnitude) :
    |(∫ u, phi u
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber g)) -
      (∫ u, phi u
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber h))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta * magnitude := by
  let μ₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber g)
  let μ₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber h)
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber g)
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber h)
  let center : ℝ := phi (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  change
    |(∫ u, phi u ∂μ₁) - (∫ u, phi u ∂μ₂)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta * magnitude
  by_cases hMagnitudeZero : magnitude = 0
  · have hConst : phi = fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => center := by
      funext u
      have hle : |phi u - center| ≤ 0 := by
        simpa [center, hMagnitudeZero] using
          hFiberVariation u (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
      have hz : |phi u - center| = 0 := le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    simp [hConst, hMagnitudeZero]
  · have hMagnitudePos : 0 < magnitude :=
      lt_of_le_of_ne hMagnitude (Ne.symm hMagnitudeZero)
    let psi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
      fun u => (phi u - center) / magnitude
    have hpsi : StronglyMeasurable psi := by
      dsimp [psi]
      simpa [div_eq_mul_inv] using
        (hphi.sub stronglyMeasurable_const).mul_const magnitude⁻¹
    have hpsiBound :
        ∀ u : Matrix.specialUnitaryGroup (Fin N) ℂ, |psi u| ≤ 1 := by
      intro u
      dsimp [psi]
      rw [abs_div, abs_of_pos hMagnitudePos]
      apply (div_le_iff₀ hMagnitudePos).2
      simpa [center] using
        hFiberVariation u (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
    have hInfluence :
        |(∫ u, psi u ∂μ₁) - (∫ u, psi u ∂μ₂)| ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta := by
      have hBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_update_distinct_background
          H N hN beta hbeta B target source fiber backgroundFiber hDistinct
          k g₂ A g h psi hpsi hpsiBound
      simpa [
        μ₁, μ₂,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence] using hBound
    have hpsiInt₁ : Integrable psi μ₁ := by
      apply (integrable_const (1 : ℝ)).mono hpsi.aestronglyMeasurable
      filter_upwards with u
      simpa [Real.norm_eq_abs] using hpsiBound u
    have hpsiInt₂ : Integrable psi μ₂ := by
      apply (integrable_const (1 : ℝ)).mono hpsi.aestronglyMeasurable
      filter_upwards with u
      simpa [Real.norm_eq_abs] using hpsiBound u
    have hIdentity₁ :
        (∫ u, phi u ∂μ₁) = magnitude * (∫ u, psi u ∂μ₁) + center := by
      calc
        (∫ u, phi u ∂μ₁) = ∫ u, magnitude * psi u + center ∂μ₁ := by
          apply integral_congr_ae
          filter_upwards [] with u
          dsimp [psi]
          field_simp [ne_of_gt hMagnitudePos]
          ring
        _ = magnitude * (∫ u, psi u ∂μ₁) + center := by
          rw [integral_add (hpsiInt₁.const_mul magnitude) (integrable_const center),
            integral_const_mul]
          simp
    have hIdentity₂ :
        (∫ u, phi u ∂μ₂) = magnitude * (∫ u, psi u ∂μ₂) + center := by
      calc
        (∫ u, phi u ∂μ₂) = ∫ u, magnitude * psi u + center ∂μ₂ := by
          apply integral_congr_ae
          filter_upwards [] with u
          dsimp [psi]
          field_simp [ne_of_gt hMagnitudePos]
          ring
        _ = magnitude * (∫ u, psi u ∂μ₂) + center := by
          rw [integral_add (hpsiInt₂.const_mul magnitude) (integrable_const center),
            integral_const_mul]
          simp
    rw [hIdentity₁, hIdentity₂]
    have hAlgebra :
        magnitude * (∫ u, psi u ∂μ₁) + center -
            (magnitude * (∫ u, psi u ∂μ₂) + center) =
          magnitude * ((∫ u, psi u ∂μ₁) - ∫ u, psi u ∂μ₂) := by
      ring
    rw [hAlgebra, abs_mul, abs_of_pos hMagnitudePos]
    calc
      magnitude * |(∫ u, psi u ∂μ₁) - ∫ u, psi u ∂μ₂| ≤
          magnitude *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta :=
        mul_le_mul_of_nonneg_left hInfluence hMagnitudePos.le
      _ =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta * magnitude := by
        ring

/-- After one literal C5 heat-bath update on `fiber`, changing a distinct
left-background coordinate propagates the original direct variation plus the
normalized conditional-law off-fiber influence times the resampled fiber
variation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_distinctBackground_variation_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : backgroundFiber ≠ fiber)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e) :
    |(∫ D, F D
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber g)) -
      (∫ D, F D
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber h))| ≤
      variation backgroundFiber +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * variation fiber := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber g) F hF,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber h) F hF]
  let μg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber g)
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber h)
  let phiG : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun u => F (Function.update (Function.update A backgroundFiber g) fiber u)
  let phiH : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun u => F (Function.update (Function.update A backgroundFiber h) fiber u)
  letI : IsProbabilityMeasure μg := by
    dsimp [μg]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber g)
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber h)
  have hUpdateG : Measurable
      (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update (Function.update A backgroundFiber g) fiber u) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  have hUpdateH : Measurable
      (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update (Function.update A backgroundFiber h) fiber u) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  have hPhiG : StronglyMeasurable phiG := by
    dsimp [phiG]
    exact hF.comp_measurable hUpdateG
  have hPhiH : StronglyMeasurable phiH := by
    dsimp [phiH]
    exact hF.comp_measurable hUpdateH
  have hPhiGVariation :
      ∀ u v : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |phiG u - phiG v| ≤ variation fiber := by
    intro u v
    simpa [phiG] using
      hVariation fiber (Function.update A backgroundFiber g) u v
  have hPhiHVariation :
      ∀ u v : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |phiH u - phiH v| ≤ variation fiber := by
    intro u v
    simpa [phiH] using
      hVariation fiber (Function.update A backgroundFiber h) u v
  have hDirectPoint :
      ∀ u : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |phiG u - phiH u| ≤ variation backgroundFiber := by
    intro u
    have hCfgG :
        Function.update (Function.update A backgroundFiber g) fiber u =
          Function.update (Function.update A fiber u) backgroundFiber g := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_update_distinct
          H N A fiber backgroundFiber hDistinct u g
    have hCfgH :
        Function.update (Function.update A backgroundFiber h) fiber u =
          Function.update (Function.update A fiber u) backgroundFiber h := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_update_distinct
          H N A fiber backgroundFiber hDistinct u h
    dsimp [phiG, phiH]
    rw [hCfgG, hCfgH]
    exact hVariation backgroundFiber (Function.update A fiber u) g h
  let centerG : ℝ := phiG (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  let centerH : ℝ := phiH (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hPhiGBound :
      ∀ u : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ‖phiG u‖ ≤ ‖variation fiber + |centerG|‖ := by
    intro u
    have hTri : |phiG u| ≤ |phiG u - centerG| + |centerG| := by
      calc
        |phiG u| = |(phiG u - centerG) + centerG| := by
          congr 1
          ring
        _ ≤ |phiG u - centerG| + |centerG| := by
          simpa [Real.norm_eq_abs] using norm_add_le (phiG u - centerG) centerG
    have hVar : |phiG u - centerG| ≤ variation fiber := by
      simpa [centerG] using
        hPhiGVariation u (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
    have hRaw : |phiG u| ≤ variation fiber + |centerG| :=
      hTri.trans (add_le_add_right hVar _)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (hVariationNonneg fiber) (abs_nonneg centerG))] using hRaw
  have hPhiHBound :
      ∀ u : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ‖phiH u‖ ≤ ‖variation fiber + |centerH|‖ := by
    intro u
    have hTri : |phiH u| ≤ |phiH u - centerH| + |centerH| := by
      calc
        |phiH u| = |(phiH u - centerH) + centerH| := by
          congr 1
          ring
        _ ≤ |phiH u - centerH| + |centerH| := by
          simpa [Real.norm_eq_abs] using norm_add_le (phiH u - centerH) centerH
    have hVar : |phiH u - centerH| ≤ variation fiber := by
      simpa [centerH] using
        hPhiHVariation u (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
    have hRaw : |phiH u| ≤ variation fiber + |centerH| :=
      hTri.trans (add_le_add_right hVar _)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (hVariationNonneg fiber) (abs_nonneg centerH))] using hRaw
  have hPhiGIntG : Integrable phiG μg := by
    apply (integrable_const (variation fiber + |centerG|)).mono hPhiG.aestronglyMeasurable
    filter_upwards with u
    exact hPhiGBound u
  have hPhiHIntG : Integrable phiH μg := by
    apply (integrable_const (variation fiber + |centerH|)).mono hPhiH.aestronglyMeasurable
    filter_upwards with u
    exact hPhiHBound u
  have hPhiHIntH : Integrable phiH μh := by
    apply (integrable_const (variation fiber + |centerH|)).mono hPhiH.aestronglyMeasurable
    filter_upwards with u
    exact hPhiHBound u
  have hDirect :
      |(∫ u, phiG u ∂μg) - (∫ u, phiH u ∂μg)| ≤ variation backgroundFiber := by
    rw [← integral_sub hPhiGIntG hPhiHIntG]
    have hDiffInt : Integrable (fun u => phiG u - phiH u) μg :=
      hPhiGIntG.sub hPhiHIntG
    have hAbsDiffInt : Integrable (fun u => |phiG u - phiH u|) μg := by
      simpa [Real.norm_eq_abs] using hDiffInt.norm
    have hConstInt : Integrable
        (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => variation backgroundFiber) μg :=
      integrable_const (variation backgroundFiber)
    calc
      |∫ u, phiG u - phiH u ∂μg| ≤ ∫ u, |phiG u - phiH u| ∂μg :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _u : Matrix.specialUnitaryGroup (Fin N) ℂ,
          variation backgroundFiber ∂μg := by
        apply integral_mono hAbsDiffInt hConstInt
        intro u
        exact hDirectPoint u
      _ = variation backgroundFiber := by simp
  have hLaw :
      |(∫ u, phiH u ∂μg) - (∫ u, phiH u ∂μh)| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * variation fiber := by
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fiberVariation_influence_update_distinct_background
        H N hN beta hbeta B target source fiber backgroundFiber hDistinct
        k g₂ A g h phiH hPhiH (variation fiber) (hVariationNonneg fiber)
        hPhiHVariation
    simpa [μg, μh] using hBound
  let x := ∫ u, phiG u ∂μg
  let y := ∫ u, phiH u ∂μg
  let z := ∫ u, phiH u ∂μh
  have hEq : x - z = (x - y) + (y - z) := by ring
  change |x - z| ≤ _
  rw [hEq]
  calc
    |(x - y) + (y - z)| ≤ |x - y| + |y - z| := by
      simpa [Real.norm_eq_abs] using norm_add_le (x - y) (y - z)
    _ ≤ variation backgroundFiber +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * variation fiber :=
      add_le_add hDirect hLaw

end

end MathlibAnalytic
end MGAP4D
