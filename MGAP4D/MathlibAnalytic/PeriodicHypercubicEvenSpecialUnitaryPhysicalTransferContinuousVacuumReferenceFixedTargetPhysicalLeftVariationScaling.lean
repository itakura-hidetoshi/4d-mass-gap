import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionFixedTargetPhysicalLeftInfluenceEnvelope
import Mathlib.Tactic

/-!
# Scale the fixed-target physical-left conditional-law influence by variation

The fixed-target law-level theorem controls bounded tests with |phi| <= 1 by
the actual fixed-target physical influence envelope.  For response propagation
we need the same estimate for an arbitrary declared oscillation magnitude.

This file performs only that normalization step.  It preserves the actual
fixed-target envelope coefficient pointwise; no coarse distinct-fiber
coefficient is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedTargetPhysicalLeftVariationScalingSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance fixedTargetPhysicalLeftVariationScalingSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The fixed-target bounded-test influence estimate scales exactly with an
arbitrary nonnegative oscillation magnitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetPhysicalLeft_fiberVariation_difference_le_envelopeKernel_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source *
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source *
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence target source := by
      have hBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetPhysicalLeft_boundedTest_difference_le_envelopeKernel
          H N hN beta hbeta B A distinguishedTarget distinguishedSource target source
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
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A distinguishedTarget).influence target source :=
        mul_le_mul_of_nonneg_left hInfluence hMagnitudePos.le
      _ =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence target source *
            magnitude := by
        ring

end

end MathlibAnalytic
end MGAP4D
