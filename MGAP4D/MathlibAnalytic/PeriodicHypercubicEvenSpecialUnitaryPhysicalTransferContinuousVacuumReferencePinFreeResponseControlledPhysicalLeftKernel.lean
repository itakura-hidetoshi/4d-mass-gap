import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinguishedTargetRemoteCrossRatio
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledWeightedRowPinObstruction
import Mathlib.Tactic

/-!
# Pin-free response-controlled physical left kernel

The older fixed-target envelope treated the distinguished target as an
unconditional Harnack exception.  The distinguished-target remote
cross-ratio theorem removes that technical exception: if the updated
background source is distinct and shares no intrinsic spatial plaquette with
the resampled fiber, the literal distinguished-target law is controlled by
the same fixed-right response majorant as every off-target remote fiber.

Accordingly the configuration-independent physical kernel can now be chosen as

* diagonal: zero;
* intrinsic active neighbor: the local Harnack coefficient;
* every other pair: exp(16 beta) times the fixed-right response profile.

There is no distinguished-target pin.

The final theorem records the resulting exponentially weighted row bound:
under a weighted response-row coefficient M, the full pin-free kernel has
coefficient
  18 * eta(beta) * s^2 + exp(16 beta) * M,
with no volume-growing extra term.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance pinFreeResponseControlledSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pinFreeResponseControlledSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Configuration-independent response-controlled physical left kernel with
no distinguished-target pin. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
        else if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta
        else
          Real.exp (16 * beta) * R target source
      influence_nonneg := by
        intro target source
        by_cases hEq : target = source
        · simp [hEq]
        · simp only [hEq, if_false]
          by_cases hActive :
              target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
          · rw [if_pos hActive]
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
                beta hbeta
          · rw [if_neg hActive]
            exact mul_nonneg (Real.exp_pos _).le (hRNonneg target source)
      influence_diagonal_zero := by
        intro source
        simp }

/-- Inactive off-diagonal spatial pairs share no intrinsic plaquette. -/
theorem
    periodicHypercubicEvenSpatialSlice_not_sharePlaquette_of_not_active
    (H : ℕ)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNotActive :
      target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source) :
    ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
  intro hShare
  apply hNotActive
  have hAdj :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj source target := by
    exact
      ⟨hne,
        (periodicHypercubicEvenSpatialSliceLinksSharePlaquette_comm
          H target source).mp hShare⟩
  exact
    (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
      H source target).mp hAdj

/-- Every literal fixed-target bounded-test update is controlled by the
pin-free response-controlled kernel.  Active pairs use local Harnack control;
all inactive pairs use the same fixed-right cross-ratio majorant, including
the distinguished target itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pinFreeResponseControlled_boundedTest_difference_le
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta R hRNonneg).influence target source := by
  classical
  by_cases hActive :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
  · have hAdj :
        (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj source target :=
      (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
        H source target).mpr hActive
    have hShare :
        periodicHypercubicEvenSpatialSliceLinksSharePlaquette H source target :=
      hAdj.2
    have hLocal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_boundedTest_difference_le_harnackInfluence
        H N hN beta hbeta B distinguishedTarget distinguishedSource target source
        hne k g₂ u v A phi hphi hphiBound
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel,
      hne, hActive, hShare] using hLocal
  · have hNoShare :
        ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source :=
      periodicHypercubicEvenSpatialSlice_not_sharePlaquette_of_not_active
        H hne hActive
    have hRemoteLaw :
        |(∫ g, phi g
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
              (Function.update A source u)) -
          (∫ g, phi g
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
              (Function.update A source v))| ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta A target source := by
      by_cases hTarget : target = distinguishedTarget
      · subst target
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_distinguishedTarget_remote_boundedTest_difference_le_worstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta B A distinguishedTarget distinguishedSource source
            hne hNoShare k g₂ u v phi hphi hphiBound
      · exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_integral_difference_abs_le_worstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta B distinguishedTarget distinguishedSource target source
            hTarget (Ne.symm hne) hNoShare k g₂ u v A phi hphi hphiBound
    have hMajorant :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta A target source ≤
          Real.exp (16 * beta) * R target source :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_of_responseBound
        H N hN beta hbeta A target source
        (R target source) (hRNonneg target source)
        (fun g₁ g₂ h k => hResponse A target source g₁ g₂ h k)
    have hNoShareRev :
        ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H source target := by
      intro hShareRev
      exact hNoShare
        ((periodicHypercubicEvenSpatialSliceLinksSharePlaquette_comm
          H target source).mpr hShareRev)
    calc
      |(∫ g, phi g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
            (Function.update A source u)) -
        (∫ g, phi g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
            (Function.update A source v))| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta A target source := hRemoteLaw
      _ ≤ Real.exp (16 * beta) * R target source := hMajorant
      _ =
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence target source := by
          simp [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel,
            hne, hActive, hNoShareRev]

/-- Pointwise, the pin-free kernel is bounded by the genuine local Harnack
kernel plus the response feedback. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_le_local_add_response
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta R hRNonneg).influence target source ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source +
      Real.exp (16 * beta) * R target source := by
  classical
  have hResponseNonneg : 0 ≤ Real.exp (16 * beta) * R target source :=
    mul_nonneg (Real.exp_pos _).le (hRNonneg target source)
  by_cases hEq : target = source
  · subst target
    change
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence source source +
        Real.exp (16 * beta) * R source source
    exact add_nonneg
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence_nonneg source source)
      hResponseNonneg
  · by_cases hActive :
        target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
    · simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel,
        hEq, if_false, hActive, if_true,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel]
      exact le_add_of_nonneg_right hResponseNonneg
    · have hLocalZero :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_influence_eq_zero_of_not_active
          H beta hbeta target source hActive
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel,
        hEq, if_false, hActive, hLocalZero, zero_add]
      exact le_rfl

/-- The pin-free response-controlled kernel has a fully volume-independent
exponentially weighted row bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_exponentialWeightedRow_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center target : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseRow :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedRowBound
        H s center R responseCoefficient) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        Real.exp (16 * beta) * responseCoefficient) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  classical
  let Klocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWeightNonneg : ∀ source, 0 ≤ W source := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg center source
  have hPointwise :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta R hRNonneg).influence target source * W source ≤
          (Klocal.influence target source +
            Real.exp (16 * beta) * R target source) * W source := by
    intro source
    exact mul_le_mul_of_nonneg_right
      (by
        simpa [Klocal] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_le_local_add_response
            H beta hbeta R hRNonneg target source)
      (hWeightNonneg source)
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_le
      H beta hbeta s hs center target
  have hResponse := hResponseRow target
  have hExpNonneg : 0 ≤ Real.exp (16 * beta) := (Real.exp_pos _).le
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence target source * W source) ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (Klocal.influence target source +
          Real.exp (16 * beta) * R target source) * W source := by
        exact Finset.sum_le_sum fun source _ => hPointwise source
    _ =
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        Klocal.influence target source * W source) +
      Real.exp (16 * beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          R target source * W source) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro source _hSource
        ring
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) * W target +
      Real.exp (16 * beta) * (responseCoefficient * W target) := by
        exact add_le_add hLocal
          (mul_le_mul_of_nonneg_left hResponse hExpNonneg)
    _ =
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        Real.exp (16 * beta) * responseCoefficient) *
        W target := by
          ring

end

end MathlibAnalytic
end MGAP4D
