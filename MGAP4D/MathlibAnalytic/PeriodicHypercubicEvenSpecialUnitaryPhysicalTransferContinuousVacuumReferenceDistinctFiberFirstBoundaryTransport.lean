import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberVariationPropagation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathDistinctFiberTransportCriterion
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberFirstBoundaryTransportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberFirstBoundaryTransportSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberFirstBoundaryTransportSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberFirstBoundaryTransportSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberFirstBoundaryTransportSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberFirstBoundaryTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A strongly measurable observable with finite oscillation along the resampled
fiber is integrable against the literal C5 one-link heat-bath transition law.
This is the local integrability receipt needed to apply Bochner Fubini to the
two-step kernel without imposing a global boundedness hypothesis. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (hFiberVariation :
      ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |F (Function.update A fiber g) - F (Function.update A fiber h)| ≤
          magnitude) :
    Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂ A
  let phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun u => F (Function.update A fiber u)
  let center : ℝ := phi (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A
  have hUpdate : Measurable
      (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update A fiber u) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  have hPhi : StronglyMeasurable phi := by
    dsimp [phi]
    exact hF.comp_measurable hUpdate
  have hPhiBound :
      ∀ u : Matrix.specialUnitaryGroup (Fin N) ℂ,
        ‖phi u‖ ≤ ‖magnitude + |center|‖ := by
    intro u
    have hTri : |phi u| ≤ |phi u - center| + |center| := by
      calc
        |phi u| = |(phi u - center) + center| := by
          congr 1
          ring
        _ ≤ |phi u - center| + |center| := by
          simpa [Real.norm_eq_abs] using norm_add_le (phi u - center) center
    have hVar : |phi u - center| ≤ magnitude := by
      simpa [phi, center] using
        hFiberVariation u (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
    have hRaw : |phi u| ≤ magnitude + |center| :=
      hTri.trans (add_le_add hVar (le_refl _))
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hMagnitude (abs_nonneg center))] using hRaw
  have hPhiInt : Integrable phi μ := by
    apply (integrable_const (magnitude + |center|)).mono hPhi.aestronglyMeasurable
    filter_upwards with u
    exact hPhiBound u
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map_fiberProbabilityMeasure]
  apply (integrable_map_measure hF.aestronglyMeasurable hUpdate.aemeasurable).2
  simpa [phi, Function.comp_def] using hPhiInt

/-- The explicit normalized literal-C5 off-fiber coefficient discharges the
`hFirstBoundary` obligation of the distinct-fiber two-step transport criterion.
The only additional analytic step is local integrability on the two updated
fibers, obtained from the same declared coordinate variation profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_firstBoundary_le
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
          H N hN beta hbeta B target source fiber₁ fiber₂ k₁ k₁ g₂ A F -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₁ g₂ A F| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₁ source *
        (variation fiber₁ +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta * variation fiber₂) := by
  let K₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber₂ k₁ g₂
  let K₁ : Matrix.specialUnitaryGroup (Fin N) ℂ →
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    fun k =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber₁ k g₂
  let magnitude : ℝ :=
    variation fiber₁ +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta * variation fiber₂
  let G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun C => ∫ D, F D ∂K₂ C
  let Gnorm : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun C => ∫ D, ‖F D‖ ∂K₂ C
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
  have hG : StronglyMeasurable G := by
    dsimp [G]
    exact hF.integral_kernel
  have hGnorm : StronglyMeasurable Gnorm := by
    dsimp [Gnorm]
    exact hF.norm.integral_kernel
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
  have hGVariation :
      ∀ u v : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |G (Function.update A fiber₁ u) - G (Function.update A fiber₁ v)| ≤ magnitude := by
    intro u v
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_distinctBackground_variation_le
        H N hN beta hbeta B target source fiber₂ fiber₁ hDistinct
        k₁ g₂ A u v F hF variation hVariationNonneg hVariation
    simpa [G, K₂, magnitude] using hBound
  have hGnormVariation :
      ∀ u v : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |Gnorm (Function.update A fiber₁ u) - Gnorm (Function.update A fiber₁ v)| ≤ magnitude := by
    intro u v
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_distinctBackground_variation_le
        H N hN beta hbeta B target source fiber₂ fiber₁ hDistinct
        k₁ g₂ A u v (fun C => ‖F C‖) hF.norm variation hVariationNonneg hNormVariation
    simpa [Gnorm, K₂, magnitude] using hBound
  have hCompIntegrable :
      ∀ kFirst : Matrix.specialUnitaryGroup (Fin N) ℂ,
        Integrable F ((K₂ ∘ₖ K₁ kFirst) A) := by
    intro kFirst
    apply (ProbabilityTheory.integrable_comp_iff hF.aestronglyMeasurable).2
    constructor
    · filter_upwards with C
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
          H N hN beta hbeta B target source fiber₂ k₁ g₂ C F hF
          (variation fiber₂) (hVariationNonneg fiber₂) (hVariation fiber₂ C)
    · simpa [Gnorm, K₁] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
          H N hN beta hbeta B target source fiber₁ kFirst g₂ A Gnorm hGnorm
          magnitude hMagnitude hGnormVariation
  have hNested :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fiberVariation_influence_le_crossBoundaryMajorant_mul
      H N hN beta hbeta B target source fiber₁ k₁ k₂ g₂ A G hG
      magnitude hMagnitude hGVariation
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
  rw [
    ProbabilityTheory.Kernel.integral_comp (hCompIntegrable k₁),
    ProbabilityTheory.Kernel.integral_comp (hCompIntegrable k₂)]
  simpa [G, K₂, K₁, magnitude] using hNested

end

end MathlibAnalytic
end MGAP4D
