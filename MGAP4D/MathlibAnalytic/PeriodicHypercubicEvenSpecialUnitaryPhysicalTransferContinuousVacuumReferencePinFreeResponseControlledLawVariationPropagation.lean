import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledWeightedRandomScanOrbit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedTargetPhysicalLeftHeatBathVariationPropagation
import Mathlib.Tactic

/-!
# Pin-free response-controlled law variation propagation

This file reconnects the pin-free response-controlled physical-left kernel to
literal law-level variation propagation.

First, the bounded-test pin-free estimate is scaled to an arbitrary declared
oscillation magnitude by centering and normalization.  Second, that law-level
estimate is inserted into the one-link heat-bath direct-plus-law decomposition.
Finally, the literal restricted random-scan expectation is propagated by the
abstract pin-free random-scan variation update introduced in the preceding
weighted-orbit unit.

No distinguished-target pin is reintroduced.  No contraction, stationary
closure, covariance decay, coercivity, or mass-gap input is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance pinFreeResponseControlledLawVariationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pinFreeResponseControlledLawVariationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pinFreeResponseControlledLawVariationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pinFreeResponseControlledLawVariationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pinFreeResponseControlledLawVariationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pinFreeResponseControlledLawVariationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The pin-free bounded-test response estimate scales exactly with an arbitrary
nonnegative oscillation magnitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pinFreeResponseControlled_fiberVariation_difference_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource target source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (hVariation :
      ∀ x y : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |phi x - phi y| ≤ magnitude) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
          (Function.update A source u)) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
          (Function.update A source v))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta R hRNonneg).influence target source *
        magnitude := by
  let μ₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
      (Function.update A source u)
  let μ₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
      (Function.update A source v)
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
        (Function.update A source u)
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
        (Function.update A source v)
  let center : ℝ := phi (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  change
    |(∫ g, phi g ∂μ₁) - (∫ g, phi g ∂μ₂)| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta R hRNonneg).influence target source *
        magnitude
  by_cases hMagnitudeZero : magnitude = 0
  · have hConst : phi = fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => center := by
      funext x
      have hle : |phi x - center| ≤ 0 := by
        simpa [center, hMagnitudeZero] using
          hVariation x (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
      have hz : |phi x - center| = 0 := le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    simp [hConst, hMagnitudeZero]
  · have hMagnitudePos : 0 < magnitude :=
      lt_of_le_of_ne hMagnitude (Ne.symm hMagnitudeZero)
    let psi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
      fun x => (phi x - center) / magnitude
    have hpsi : StronglyMeasurable psi := by
      dsimp [psi]
      simpa [div_eq_mul_inv] using
        (hphi.sub stronglyMeasurable_const).mul_const magnitude⁻¹
    have hpsiBound :
        ∀ x : Matrix.specialUnitaryGroup (Fin N) ℂ, |psi x| ≤ 1 := by
      intro x
      dsimp [psi]
      rw [abs_div, abs_of_pos hMagnitudePos]
      apply (div_le_iff₀ hMagnitudePos).2
      simpa [center] using
        hVariation x (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
    have hInfluence :
        |(∫ x, psi x ∂μ₁) - (∫ x, psi x ∂μ₂)| ≤
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta R hRNonneg).influence target source := by
      have hBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pinFreeResponseControlled_boundedTest_difference_le
          H N hN beta hbeta R hRNonneg hResponse B A distinguishedTarget distinguishedSource target source
          hne k g₂ u v psi hpsi hpsiBound
      simpa [μ₁, μ₂] using hBound
    have hpsiInt₁ : Integrable psi μ₁ := by
      apply (integrable_const (1 : ℝ)).mono hpsi.aestronglyMeasurable
      filter_upwards with x
      simpa [Real.norm_eq_abs] using hpsiBound x
    have hpsiInt₂ : Integrable psi μ₂ := by
      apply (integrable_const (1 : ℝ)).mono hpsi.aestronglyMeasurable
      filter_upwards with x
      simpa [Real.norm_eq_abs] using hpsiBound x
    have hIdentity₁ :
        (∫ x, phi x ∂μ₁) = magnitude * (∫ x, psi x ∂μ₁) + center := by
      calc
        (∫ x, phi x ∂μ₁) = ∫ x, magnitude * psi x + center ∂μ₁ := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [psi]
          field_simp [ne_of_gt hMagnitudePos]
          ring
        _ = magnitude * (∫ x, psi x ∂μ₁) + center := by
          rw [integral_add (hpsiInt₁.const_mul magnitude) (integrable_const center),
            integral_const_mul]
          simp
    have hIdentity₂ :
        (∫ x, phi x ∂μ₂) = magnitude * (∫ x, psi x ∂μ₂) + center := by
      calc
        (∫ x, phi x ∂μ₂) = ∫ x, magnitude * psi x + center ∂μ₂ := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [psi]
          field_simp [ne_of_gt hMagnitudePos]
          ring
        _ = magnitude * (∫ x, psi x ∂μ₂) + center := by
          rw [integral_add (hpsiInt₂.const_mul magnitude) (integrable_const center),
            integral_const_mul]
          simp
    rw [hIdentity₁, hIdentity₂]
    have hAlgebra :
        magnitude * (∫ x, psi x ∂μ₁) + center -
            (magnitude * (∫ x, psi x ∂μ₂) + center) =
          magnitude * ((∫ x, psi x ∂μ₁) - ∫ x, psi x ∂μ₂) := by
      ring
    rw [hAlgebra, abs_mul, abs_of_pos hMagnitudePos]
    calc
      magnitude * |(∫ x, psi x ∂μ₁) - ∫ x, psi x ∂μ₂| ≤
          magnitude *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta R hRNonneg).influence target source :=
        mul_le_mul_of_nonneg_left hInfluence hMagnitudePos.le
      _ =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta R hRNonneg).influence target source *
            magnitude := by
        ring

/-- After one literal heat-bath update, changing a distinct left-background
coordinate propagates direct variation plus the pin-free response-controlled
conditional-law influence times the resampled-fiber variation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_pinFreeResponseControlled_distinctBackground_variation_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence
            fiber backgroundFiber * variation fiber := by
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pinFreeResponseControlled_fiberVariation_difference_le
        H N hN beta hbeta R hRNonneg hResponse B A distinguishedTarget distinguishedSource fiber backgroundFiber
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence
            fiber backgroundFiber * variation fiber :=
      add_le_add hDirect hLaw

/-- One actual restricted random-scan step propagates left-fiber variation by
the pin-free response-controlled physical kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_fiberVariation_le_pinFreeResponseControlled
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k (Function.update A e u) F -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k (Function.update A e v) F| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
        H beta hbeta R hRNonneg variation e := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta R hRNonneg
  have hInvNonneg :
      0 ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ [fiber] k
          (Function.update A e u) F -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ [fiber] k
          (Function.update A e v) F| ≤
        finiteInfluenceKernelUpdatedVariation K variation fiber e := by
    by_cases hEq : e = fiber
    · subst e
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_nil]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_update_fiber
          H N hN beta hbeta B target source fiber k g₂ A u,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_update_fiber
          H N hN beta hbeta B target source fiber k g₂ A v]
      simp [finiteInfluenceKernelUpdatedVariation]
    · have hBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_pinFreeResponseControlled_distinctBackground_variation_le
          H N hN beta hbeta R hRNonneg hResponse
          B target source fiber e hEq k g₂ A u v F hF
          variation hVariationNonneg hVariation
      simpa [
        K,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation,
        finiteInfluenceKernelUpdatedVariation,
        hEq] using hBound
  have hSum :
      |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e u) F -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e v) F)| ≤
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation K variation fiber e := by
    calc
      |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e u) F -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e v) F)| ≤
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e u) F -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e v) F| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation K variation fiber e := by
        apply Finset.sum_le_sum
        intro fiber _hFiber
        exact hTarget fiber
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  change
    |(Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e u) F) -
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e v) F)| ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation K variation fiber e
  calc
    |(Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e u) F) -
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e v) F)| =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e u) F -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k
              (Function.update A e v) F)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation K variation fiber e :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

end

end MathlibAnalytic
end MGAP4D
