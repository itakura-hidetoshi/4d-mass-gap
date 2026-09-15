import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathRow
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceCrossBoundaryHeatBathVariationInfluenceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceCrossBoundaryHeatBathVariationInfluenceSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceCrossBoundaryHeatBathVariationInfluenceSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceCrossBoundaryHeatBathVariationInfluenceSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceCrossBoundaryHeatBathVariationInfluenceSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceCrossBoundaryHeatBathVariationInfluenceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The proved C5 heat-bath cross-boundary influence scales with an actual
fiber-variation radius, not merely a global `|F| ≤ 1` normalization.

This is the continuous-state local input needed by the kernel-response lane:
changing a right-boundary source value affects the resampled left fiber by at
most the already-proved one-way C5 majorant times the declared oscillation of
the observable along that fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fiberVariation_influence_le_crossBoundaryMajorant_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (hFiberVariation :
      ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |F (Function.update A fiber g) - F (Function.update A fiber h)| ≤
          magnitude) :
    |(∫ C, F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k₁ g₂ A) -
      (∫ C, F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k₂ g₂ A)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source * magnitude := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B target source fiber k₁ g₂ A F hF,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integral
      H N hN beta hbeta B target source fiber k₂ g₂ A F hF]
  let h : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => F (Function.update A fiber g)
  let μ₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k₁ g₂ A
  let μ₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k₂ g₂ A
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k₁ g₂ A
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k₂ g₂ A
  have hUpdate : Measurable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update A fiber g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  have hh : StronglyMeasurable h := by
    dsimp [h]
    exact hF.comp_measurable hUpdate
  let center : ℝ := h (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  change
    |(∫ g, h g ∂μ₁) - (∫ g, h g ∂μ₂)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source * magnitude
  by_cases hMagnitudeZero : magnitude = 0
  · have hConst : h = fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => center := by
      funext g
      have hle : |h g - center| ≤ 0 := by
        simpa [h, center, hMagnitudeZero] using
          hFiberVariation g (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
      have hz : |h g - center| = 0 := le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    simp [hConst, hMagnitudeZero]
  · have hMagnitudePos : 0 < magnitude :=
      lt_of_le_of_ne hMagnitude (Ne.symm hMagnitudeZero)
    let phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
      fun g => (h g - center) / magnitude
    have hphi : StronglyMeasurable phi := by
      dsimp [phi]
      simpa [div_eq_mul_inv] using
        (hh.sub stronglyMeasurable_const).mul_const magnitude⁻¹
    have hphiBound :
        ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ, |phi g| ≤ 1 := by
      intro g
      dsimp [phi]
      rw [abs_div, abs_of_pos hMagnitudePos]
      apply (div_le_iff₀ hMagnitudePos).2
      simpa [h, center] using
        hFiberVariation g (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
    have hInfluence :
        |(∫ g, phi g ∂μ₁) - (∫ g, phi g ∂μ₂)| ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source := by
      have hBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_supported_on_diagonal
          H N hN beta hbeta B target source fiber k₁ k₂ g₂ A
          phi hphi hphiBound
      simpa [
        μ₁, μ₂,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant] using hBound
    have hphiInt₁ : Integrable phi μ₁ := by
      apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
      filter_upwards with g
      simpa [Real.norm_eq_abs] using hphiBound g
    have hphiInt₂ : Integrable phi μ₂ := by
      apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
      filter_upwards with g
      simpa [Real.norm_eq_abs] using hphiBound g
    have hIdentity₁ :
        (∫ g, h g ∂μ₁) = magnitude * (∫ g, phi g ∂μ₁) + center := by
      calc
        (∫ g, h g ∂μ₁) = ∫ g, magnitude * phi g + center ∂μ₁ := by
          apply integral_congr_ae
          filter_upwards [] with g
          dsimp [phi]
          field_simp [ne_of_gt hMagnitudePos]
          ring
        _ = magnitude * (∫ g, phi g ∂μ₁) + center := by
          rw [integral_add (hphiInt₁.const_mul magnitude) (integrable_const center),
            integral_const_mul]
          simp
    have hIdentity₂ :
        (∫ g, h g ∂μ₂) = magnitude * (∫ g, phi g ∂μ₂) + center := by
      calc
        (∫ g, h g ∂μ₂) = ∫ g, magnitude * phi g + center ∂μ₂ := by
          apply integral_congr_ae
          filter_upwards [] with g
          dsimp [phi]
          field_simp [ne_of_gt hMagnitudePos]
          ring
        _ = magnitude * (∫ g, phi g ∂μ₂) + center := by
          rw [integral_add (hphiInt₂.const_mul magnitude) (integrable_const center),
            integral_const_mul]
          simp
    rw [hIdentity₁, hIdentity₂]
    have hAlgebra :
        magnitude * (∫ g, phi g ∂μ₁) + center -
            (magnitude * (∫ g, phi g ∂μ₂) + center) =
          magnitude * ((∫ g, phi g ∂μ₁) - ∫ g, phi g ∂μ₂) := by
      ring
    rw [hAlgebra, abs_mul, abs_of_pos hMagnitudePos]
    calc
      magnitude * |(∫ g, phi g ∂μ₁) - ∫ g, phi g ∂μ₂| ≤
          magnitude *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
              beta fiber source :=
        mul_le_mul_of_nonneg_left hInfluence hMagnitudePos.le
      _ =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source * magnitude := by
        ring

end

end MathlibAnalytic
end MGAP4D