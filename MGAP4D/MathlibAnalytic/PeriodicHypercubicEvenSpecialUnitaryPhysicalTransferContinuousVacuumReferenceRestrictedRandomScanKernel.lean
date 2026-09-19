import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullHaarRefreshSweep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRestrictedRandomScanTransport
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceRestrictedRandomScanKernelSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanKernelSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanKernelSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanKernelSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanKernelSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanKernelSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N


/-- The exact uniform random-scan coefficient on the finite physical left-link
set, represented in the measure scalar field. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
    (H : ℕ) : ℝ≥0∞ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞)⁻¹

/-- Sum of all actual one-link reference heat-bath kernels.  This is left
unnormalized so that the uniform random-scan normalization is explicit in a
single place. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernelSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Kernel.sum fun fiber : PeriodicHypercubicEvenSpatialSliceLink H =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂

/-- The finite sum of actual one-link heat-bath kernels is s-finite.  We prove
this through the pinned finite-sum interface explicitly instead of relying on
implicit synthesis of the dependent family required by `Kernel.sum`. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernelSum_isSFiniteKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsSFiniteKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernelSum
        H N hN beta hbeta B target source k g₂) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernelSum
  rw [Kernel.sum_fintype]
  exact
    Kernel.IsSFiniteKernel.finset_sum Finset.univ (by
      intro fiber _
      infer_instance)

/-- Actual continuous-C5 uniform restricted random-scan Markov kernel.

It is the normalized finite sum of the exact one-link heat-bath kernels already
used by the observable-level restricted random-scan expectation.  No
covariance-decay, remote-smallness, or sweep-contraction input enters this
definition. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Kernel.withDensity
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernelSum
      H N hN beta hbeta B target source k g₂)
    (fun _ _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
        H)

/-- Pointwise measure formula for the normalized random-scan kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
        H N hN beta hbeta B target source k g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
          H •
        (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B target source fiber k g₂ A) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernelSum
  rw [Kernel.withDensity_apply _ measurable_const]
  rw [Measure.withDensity_const]
  rw [Kernel.sum_fintype]
  rw [Kernel.finset_sum_apply]

/-- The actual restricted random-scan kernel is Markov. -/
instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
        H N hN beta hbeta B target source k g₂) := by
  refine ⟨fun A => ⟨?_⟩⟩
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_apply]
  have hCardPos :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hCardNe :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCardPos
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
  simp only [Measure.smul_apply, MeasurableSet.univ,
    Finset.sum_apply, Measure.finset_sum_apply, measure_univ]
  rw [Finset.sum_const, Finset.card_univ]
  exact ENNReal.inv_mul_cancel hCardNe (by simp)

/-- Each concrete one-link update appears in the random-scan kernel with exactly
the uniform selection weight.  This is the kernel-order input used later to
embed one prescribed complete sweep into a finite random-scan block. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_lower_bound_selectedOneLink
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
        H •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
      H N hN beta hbeta B target source k g₂ A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_apply]
  apply Measure.le_iff.2
  intro s hs
  simp only [Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  apply mul_le_mul_left'
  exact
    Finset.single_le_sum
      (fun e _ => measure_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source e k g₂ A)
        s)
      (Finset.mem_univ fiber)

/-- The normalized continuous-vacuum reference law remains stationary under
the actual restricted random-scan kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_comp_referenceProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
        H N hN beta hbeta B target source k g₂ ∘ₘ
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_apply]
  have hCardPos :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hCardNe :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCardPos
  have hCardTop :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞) ≠ ∞ := by
    simp
  have hFiberMeas :
      ∀ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        Measurable
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k g₂ A s) := by
    intro fiber
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂).measurable_coe hs
  have hFiberInv :
      ∀ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        (∫⁻ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k g₂ A s
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ s := by
    intro fiber
    rw [← Measure.bind_apply hs (Kernel.aemeasurable _)]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_comp_referenceProbabilityMeasure]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
  simp_rw [Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  rw [
    lintegral_const_mul _
      (Finset.measurable_fun_sum Finset.univ (fun fiber _ => hFiberMeas fiber)),
    lintegral_finset_sum Finset.univ (fun fiber _ => hFiberMeas fiber)]
  simp_rw [hFiberInv]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hCardNe hCardTop, one_mul]

end

end MathlibAnalytic
end MGAP4D
