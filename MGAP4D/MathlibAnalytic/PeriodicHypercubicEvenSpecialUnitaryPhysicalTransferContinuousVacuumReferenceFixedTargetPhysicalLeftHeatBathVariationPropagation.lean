import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedTargetPhysicalLeftVariationScaling
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberVariationPropagation
import Mathlib.Tactic

/-!
# One-step heat-bath variation through the fixed-target physical envelope

For one literal reference heat-bath update at `fiber`, changing a distinct
left-background coordinate has two contributions:

* the direct variation at the changed background coordinate;
* the change of the conditional law, multiplied by the variation at the
  resampled fiber.

The preceding fixed-target scaling theorem controls the second contribution by
the actual fixed-target physical envelope rather than the coarse all-to-all
distinct-fiber coefficient.

This is a one-step law-level statement.  The envelope still depends on the
base configuration `A`; no configuration-uniform majorant is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedTargetPhysicalLeftHeatBathVariationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance fixedTargetPhysicalLeftHeatBathVariationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- After one heat-bath update on `fiber`, changing a distinct left-background
coordinate propagates direct variation plus the actual fixed-target physical
influence times the fiber variation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fixedTargetPhysicalLeft_distinctBackground_variation_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
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
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber g)) -
      (∫ D, F D
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber h))| ≤
      variation backgroundFiber +
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A distinguishedTarget).influence
            fiber backgroundFiber * variation fiber := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber g) F hF,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber h) F hF]
  let μg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber g)
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber h)
  let phiG : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun u => F (Function.update (Function.update A backgroundFiber g) fiber u)
  let phiH : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun u => F (Function.update (Function.update A backgroundFiber h) fiber u)
  letI : IsProbabilityMeasure μg := by
    dsimp [μg]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
        (Function.update A backgroundFiber g)
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
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
      hTri.trans (add_le_add hVar (le_refl _))
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
      hTri.trans (add_le_add hVar (le_refl _))
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A distinguishedTarget).influence
            fiber backgroundFiber * variation fiber := by
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetPhysicalLeft_fiberVariation_difference_le_envelopeKernel_mul
        H N hN beta hbeta B A distinguishedTarget distinguishedSource fiber backgroundFiber
        (Ne.symm hDistinct) k g₂ g h phiH hPhiH
        (variation fiber) (hVariationNonneg fiber) hPhiHVariation
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A distinguishedTarget).influence
            fiber backgroundFiber * variation fiber :=
      add_le_add hDirect hLaw

end

end MathlibAnalytic
end MGAP4D
