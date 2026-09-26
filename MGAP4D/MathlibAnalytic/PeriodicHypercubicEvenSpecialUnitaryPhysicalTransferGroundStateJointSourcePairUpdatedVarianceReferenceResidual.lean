import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairUpdatedVarianceStationarityReturn
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkOffFiberMeasurable
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFubiniCompatibility
import Mathlib.Tactic

/-!
# Updated target variance as an exact reference-law target residual

PR #4793 returns the ordered updated target variance to the original
source-reference background law.  The remaining quantity is still written as a
fiber variance.

This file identifies that fiber variance with the exact one-link heat-bath
projection residual under the same reference law.

For the right section

  f(A) = F(left,A)

and the target one-link reference projection P_target^ref, we prove

  ∫ ofReal(updatedBackgroundVariance(A)) d mu_source(A)
    =
  ∫ ofReal((f(A) - P_target^ref f(A))^2) d mu_source(A).

The proof is exact.  It uses only the literal target-fiber mean from PR #4781,
the measurable reference heat-bath kernel, fiber-update invariance of its
projection, and the existing full-law one-link Fubini compatibility.

No Harnack factor, triangle inequality, response coefficient, factor two, or
finite-cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance updatedVarianceReferenceResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance updatedVarianceReferenceResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance updatedVarianceReferenceResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance updatedVarianceReferenceResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance updatedVarianceReferenceResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance updatedVarianceReferenceResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise pushforward form of the periodic continuous-vacuum reference
one-link heat-bath kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A =
      Measure.map
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A) := by
  ext s hs
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel,
    Kernel.map_apply'
      (Kernel.id ×ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber)
      A hs,
    Kernel.id_prod_apply'
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂)
      A
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber) hs),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply,
    Measure.map_apply (measurable_update A) hs]
  rfl

/-- Bochner projection through the full reference heat-bath kernel is exactly
the literal one-link fiber integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_eq_fiberIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ f A =
      ∫ g,
        f (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A]
  exact
    MeasureTheory.integral_map
      (measurable_update A).aemeasurable
      hf.aestronglyMeasurable

/-- The reference heat-bath projection is unchanged when the input
configuration is modified at the same resampled fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_update_fiber
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ f
        (Function.update A fiber g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ f A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_eq_representative_comp_restriction]
  simp only [Function.comp_apply]
  congr 1
  funext e
  simp [
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberRestriction,
    e.2]

/-- At one source-reference background A, the updated target variance is the
extended squared residual of the target reference heat-bath projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy_ofReal_eq_referenceTargetResidual_fiberLIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left A) =
      ∫⁻ g,
        ENNReal.ofReal
          ((F (left, Function.update A target g) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource target k g₂
                (fun C => F (left, C)) A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ A := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun C => F (left, C)
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => rightF (Function.update A target g)
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ A
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
      H N hN beta hbeta B source distinguishedSource target k g₂ rightF
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ A
  have hRightStrong : StronglyMeasurable rightF :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hXStrong : StronglyMeasurable X :=
    hRightStrong.comp_measurable (measurable_update A)
  have hXBound : ∀ g, ‖X g‖ ≤ |bound| := by
    intro g
    exact (hbound (left, Function.update A target g)).trans (le_abs_self bound)
  have hXLp : MemLp X 2 μ :=
    MemLp.of_bound hXStrong.aestronglyMeasurable |bound|
      (Filter.Eventually.of_forall hXBound)
  have hProjection :
      P A = ∫ g, X g ∂μ := by
    simpa [P, X, rightF, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_eq_fiberIntegral
        H N hN beta hbeta B source distinguishedSource target k g₂
        rightF hRightStrong A
  have hMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂ F left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundCanonicalSection
            H N source A) =
        ∫ g, X g ∂μ := by
    have hLiteral :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean_eq_literal
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundCanonicalSection
          H N source A)
    simpa [
      X, rightF, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundCanonicalSection,
      Function.update_eq_self] using hLiteral
  have hEnergy :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left A =
        ∫ g,
          (X g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
              H N hN beta hbeta B distinguishedSource source target k g₂ F left
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundCanonicalSection
                H N source A)) ^ 2
          ∂μ := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondCenteredEnergy
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply]
    simp [
      X, rightF, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundCanonicalSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update,
      Function.update_eq_self]
  have hVariance :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left A =
        variance X μ := by
    rw [hEnergy, hMean]
    exact (variance_eq_integral hXStrong.aemeasurable).symm
  calc
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left A) =
      evariance X μ := by
        rw [hVariance]
        exact hXLp.ofReal_variance_eq
    _ =
      ∫⁻ g, ENNReal.ofReal ((X g - ∫ h, X h ∂μ) ^ 2) ∂μ := by
        rw [evariance_eq_lintegral_ofReal]
    _ =
      ∫⁻ g,
        ENNReal.ofReal
          ((F (left, Function.update A target g) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource target k g₂
                (fun C => F (left, C)) A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ A := by
        apply lintegral_congr
        intro g
        rw [← hProjection]

/-- Exact outer-law identity: the stationarity-returned updated target variance
is the squared target reference heat-bath residual under the same source
reference law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_reference_updatedBackgroundVarianceEnergy_lintegral_eq_referenceTargetResidual_sq_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource k g₂) =
      ∫⁻ A,
        ENNReal.ofReal
          ((F (left, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource target k g₂
                (fun C => F (left, C)) A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun C => F (left, C)
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
      H N hN beta hbeta B source distinguishedSource target k g₂ rightF
  let residualSq :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A => ENNReal.ofReal ((rightF A - P A) ^ 2)
  have hRightStrong : StronglyMeasurable rightF :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hPStrong : StronglyMeasurable P := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_stronglyMeasurable
        H N hN beta hbeta B source distinguishedSource target k g₂ rightF hRightStrong
  have hResidualSq : Measurable residualSq := by
    exact ENNReal.continuous_ofReal.measurable.comp
      ((hRightStrong.sub hPStrong).measurable.pow_const 2)
  calc
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource k g₂) =
      ∫⁻ A,
        ∫⁻ g,
          residualSq (Function.update A target g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ := by
      apply lintegral_congr
      intro A
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy_ofReal_eq_referenceTargetResidual_fiberLIntegral
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left A]
      apply lintegral_congr
      intro g
      unfold residualSq
      change
        ENNReal.ofReal ((rightF (Function.update A target g) - P A) ^ 2) =
          ENNReal.ofReal
            ((rightF (Function.update A target g) -
                P (Function.update A target g)) ^ 2)
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_update_fiber
          H N hN beta hbeta B source distinguishedSource target k g₂
          rightF A g]
    _ =
      ∫⁻ A, residualSq A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
        H N hN beta hbeta B source distinguishedSource target k g₂ residualSq hResidualSq
    _ =
      ∫⁻ A,
        ENNReal.ofReal
          ((F (left, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource target k g₂
                (fun C => F (left, C)) A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ := by
      rfl

end

end MGAP4D.MathlibAnalytic
