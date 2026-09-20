import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceWeightedRemoteResidualResponseLinearization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedTargetPhysicalLeftHeatBathVariationPropagation
import Mathlib.Tactic

/-!
# Configuration-independent fixed-target envelope controlled by response profiles

The actual fixed-target physical-left envelope depends on the base
configuration through its remote residual.  This is the remaining obstruction
to feeding the exact law-level variation theorem into the generic finite-kernel
iteration machinery.

A response profile `R target source` that bounds every fixed-right
target-ratio response, uniformly in the base configuration and in the four
SU(N) test values, gives a configuration-independent replacement:

* diagonal: zero;
* C5 exceptional region: the literal local Harnack coefficient;
* C5 remote region: `exp (16 * beta) * R target source`.

The remote domination is the carrier-free linearization proved in the preceding
unit.  No coarse all-to-all distinct-fiber coefficient is introduced.

This file proves that the actual configuration-dependent envelope is pointwise
dominated by this response-controlled kernel and transports both bounded-test
and arbitrary-variation one-link estimates to it.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedTargetResponseControlledEnvelopeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance fixedTargetResponseControlledEnvelopeSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- A pair profile that uniformly bounds every literal fixed-right target-ratio
response over all base configurations and all four SU(N) test values. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ) : Prop :=
  ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
      ∀ g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta A target source g₁ g₂ h k ≤
          R target source

/-- The configuration-independent response-controlled fixed-target kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source) :
    FiniteNonnegativeInfluenceKernelData
      (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact
    { influence := fun target source =>
        if target = source then 0
        else if target ∈
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget then
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta
        else
          Real.exp (16 * beta) * R target source
      influence_nonneg := by
        intro target source
        by_cases hEq : target = source
        · simp [hEq]
        · simp only [hEq, if_false]
          by_cases hExceptional :
              target ∈
                periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
                  H source distinguishedTarget
          · rw [if_pos hExceptional]
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
                beta hbeta
          · rw [if_neg hExceptional]
            exact mul_nonneg (Real.exp_pos _).le (hRNonneg target source)
      influence_diagonal_zero := by
        intro source
        simp }

/-- On an arbitrary C5-remote pair, the actual remote residual is controlled
by the uniform fixed-right response profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_le_exp_sixteen_mul_uniformResponseProfile
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
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source distinguishedTarget) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source distinguishedTarget target ≤
      Real.exp (16 * beta) * R target source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
  rw [if_pos hRemote]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_of_responseBound
      H N hN beta hbeta A target source
      (R target source) (hRNonneg target source)
      (fun g₁ g₂ h k => hResponse A target source g₁ g₂ h k)

/-- Every actual fixed-target physical-left envelope is pointwise dominated by
the same configuration-independent response-controlled kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_le_responseControlled
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
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget target source :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
        H beta hbeta distinguishedTarget R hRNonneg).influence target source := by
  classical
  by_cases hEq : target = source
  · subst target
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel]
  · by_cases hExceptional :
      target ∈
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source distinguishedTarget
    · simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel,
        hEq, hExceptional]
    · have hRemote :
          target ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
              H source distinguishedTarget := by
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
          hExceptional
      have hBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_le_exp_sixteen_mul_uniformResponseProfile
          H N hN beta hbeta R hRNonneg hResponse A
          source distinguishedTarget target hRemote
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel,
        hEq, hExceptional] using hBound

/-- The exact fixed-target bounded-test law-level estimate is therefore
dominated by the configuration-independent response-controlled kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetResponseControlled_boundedTest_difference_le
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
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
          (Function.update A source u)) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
          (Function.update A source v))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
        H beta hbeta distinguishedTarget R hRNonneg).influence target source := by
  have hActual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetPhysicalLeft_boundedTest_difference_le_envelopeKernel
      H N hN beta hbeta B A distinguishedTarget distinguishedSource target source
      hne k g₂ u v phi hphi hphiBound
  exact hActual.trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_le_responseControlled
      H N hN beta hbeta R hRNonneg hResponse A distinguishedTarget target source)

/-- The arbitrary-variation law-level estimate is also dominated by the same
configuration-independent response-controlled kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetResponseControlled_fiberVariation_difference_le
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
        H beta hbeta distinguishedTarget R hRNonneg).influence target source *
        magnitude := by
  have hActual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetPhysicalLeft_fiberVariation_difference_le_envelopeKernel_mul
      H N hN beta hbeta B A distinguishedTarget distinguishedSource target source
      hne k g₂ u v phi hphi magnitude hMagnitude hVariation
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_le_responseControlled
      H N hN beta hbeta R hRNonneg hResponse A distinguishedTarget target source
  exact hActual.trans (mul_le_mul_of_nonneg_right hKernel hMagnitude)

/-- One literal heat-bath update propagates left-background variation through
the configuration-independent response-controlled kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_responseControlled_distinctBackground_variation_le
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
          H beta hbeta distinguishedTarget R hRNonneg).influence
            fiber backgroundFiber * variation fiber := by
  have hActual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fixedTargetPhysicalLeft_distinctBackground_variation_le
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber backgroundFiber
      hDistinct k g₂ A g h F hF variation hVariationNonneg hVariation
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_le_responseControlled
      H N hN beta hbeta R hRNonneg hResponse A distinguishedTarget fiber backgroundFiber
  exact hActual.trans
    (add_le_add
      (le_refl _)
      (mul_le_mul_of_nonneg_right hKernel (hVariationNonneg fiber)))

end

end MathlibAnalytic
end MGAP4D
