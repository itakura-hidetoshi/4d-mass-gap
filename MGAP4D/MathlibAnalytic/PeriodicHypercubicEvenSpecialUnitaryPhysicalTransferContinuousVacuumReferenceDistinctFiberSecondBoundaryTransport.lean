import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberFirstBoundaryTransport
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberSecondBoundaryTransportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberSecondBoundaryTransportSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberSecondBoundaryTransportSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberSecondBoundaryTransportSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberSecondBoundaryTransportSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberSecondBoundaryTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- With the first distinct-fiber update already fixed at `k₂`, changing only
 the boundary parameter of the second update from `k₁` to `k₂` costs exactly
 the existing one-link continuous-C5 cross-boundary coefficient at `fiber₂`.

 The off-fiber estimate enters only to supply the local integrability receipt
 needed by `Kernel.integral_comp`; it does not enlarge the final coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_secondBoundary_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber₁ fiber₂ : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber₁ ≠ fiber₂)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₁ g₂ A F -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₂ g₂ A F| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₂ source * variation fiber₂ := by
  let K₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber₁ k₂ g₂
  let K₂ : Matrix.specialUnitaryGroup (Fin N) ℂ →
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    fun k =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber₂ k g₂
  let magnitude : ℝ :=
    variation fiber₁ +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta * variation fiber₂
  let G : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun k C => ∫ D, F D ∂K₂ k C
  let Gnorm : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun k C => ∫ D, ‖F D‖ ∂K₂ k C
  let bound : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
      beta fiber₂ source * variation fiber₂
  have hInfluenceNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
      beta hbeta
  have hMagnitude : 0 ≤ magnitude := by
    dsimp [magnitude]
    exact add_nonneg (hVariationNonneg fiber₁)
      (mul_nonneg hInfluenceNonneg (hVariationNonneg fiber₂))
  have hNormVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |‖F (Function.update C e u)‖ - ‖F (Function.update C e v)‖| ≤ variation e := by
    intro e C u v
    calc
      |‖F (Function.update C e u)‖ - ‖F (Function.update C e v)‖| ≤
          ‖F (Function.update C e u) - F (Function.update C e v)‖ :=
        abs_norm_sub_norm_le _ _
      _ = |F (Function.update C e u) - F (Function.update C e v)| :=
        Real.norm_eq_abs _
      _ ≤ variation e := hVariation e C u v
  have hG :
      ∀ k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        StronglyMeasurable (G k) := by
    intro k
    dsimp [G]
    exact hF.integral_kernel
  have hGnorm :
      ∀ k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        StronglyMeasurable (Gnorm k) := by
    intro k
    dsimp [Gnorm]
    exact hF.norm.integral_kernel
  have hGnormVariation :
      ∀ (k : Matrix.specialUnitaryGroup (Fin N) ℂ)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |Gnorm k (Function.update A fiber₁ u) -
          Gnorm k (Function.update A fiber₁ v)| ≤ magnitude := by
    intro k u v
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_distinctBackground_variation_le
        H N hN beta hbeta B target source fiber₂ fiber₁ hDistinct
        k g₂ A u v (fun C => ‖F C‖) hF.norm variation hVariationNonneg hNormVariation
    simpa [Gnorm, K₂, magnitude] using hBound
  have hGnormIntegrable :
      ∀ k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        Integrable (Gnorm k) (K₁ A) := by
    intro k
    simpa [K₁] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
        H N hN beta hbeta B target source fiber₁ k₂ g₂ A (Gnorm k) (hGnorm k)
        magnitude hMagnitude (hGnormVariation k)
  have hInnerIntegrable :
      ∀ k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ∀ᵐ C ∂K₁ A, Integrable F (K₂ k C) := by
    intro k
    filter_upwards with C
    simpa [K₂] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
        H N hN beta hbeta B target source fiber₂ k g₂ C F hF
        (variation fiber₂) (hVariationNonneg fiber₂) (hVariation fiber₂ C)
  have hCompIntegrable :
      ∀ k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        Integrable F ((K₂ k ∘ₖ K₁) A) := by
    intro k
    apply (ProbabilityTheory.integrable_comp_iff hF.aestronglyMeasurable).2
    exact ⟨hInnerIntegrable k, hGnormIntegrable k⟩
  have hGIntegrable :
      ∀ k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        Integrable (G k) (K₁ A) := by
    intro k
    apply (hGnormIntegrable k).mono (hG k).aestronglyMeasurable
    filter_upwards with C
    change
      ‖∫ D, F D ∂K₂ k C‖ ≤
        ‖∫ D, ‖F D‖ ∂K₂ k C‖
    have hNonneg : 0 ≤ ∫ D, ‖F D‖ ∂K₂ k C := by
      positivity
    calc
      ‖∫ D, F D ∂K₂ k C‖ ≤ ∫ D, ‖F D‖ ∂K₂ k C :=
        norm_integral_le_integral_norm _
      _ = ‖∫ D, ‖F D‖ ∂K₂ k C‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  have hPoint :
      ∀ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G k₁ C - G k₂ C| ≤ bound := by
    intro C
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fiberVariation_influence_le_crossBoundaryMajorant_mul
        H N hN beta hbeta B target source fiber₂ k₁ k₂ g₂ C F hF
        (variation fiber₂) (hVariationNonneg fiber₂) (hVariation fiber₂ C)
    simpa [G, K₂, bound] using hBound
  have hDiffIntegrable :
      Integrable (fun C => G k₁ C - G k₂ C) (K₁ A) :=
    (hGIntegrable k₁).sub (hGIntegrable k₂)
  have hAverage :
      |(∫ C, G k₁ C ∂K₁ A) - (∫ C, G k₂ C ∂K₁ A)| ≤ bound := by
    calc
      |(∫ C, G k₁ C ∂K₁ A) - (∫ C, G k₂ C ∂K₁ A)| =
          |∫ C, (G k₁ C - G k₂ C) ∂K₁ A| := by
        rw [integral_sub (hGIntegrable k₁) (hGIntegrable k₂)]
      _ = ‖∫ C, (G k₁ C - G k₂ C) ∂K₁ A‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∫ C, ‖G k₁ C - G k₂ C‖ ∂K₁ A :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _C, bound ∂K₁ A := by
        apply integral_mono_ae hDiffIntegrable.norm (integrable_const bound)
        filter_upwards with C
        simpa [Real.norm_eq_abs] using hPoint C
      _ = bound := by
        simp
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
  rw [
    ProbabilityTheory.Kernel.integral_comp (hCompIntegrable k₁),
    ProbabilityTheory.Kernel.integral_comp (hCompIntegrable k₂)]
  simpa [G, K₁, K₂, bound] using hAverage

end

end MathlibAnalytic
end MGAP4D
