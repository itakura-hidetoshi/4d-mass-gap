import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCovarianceNormalForm
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter

noncomputable section

local instance twoStepTerminalCrossingDenominatorFloorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoStepTerminalCrossingDenominatorFloorSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoStepTerminalCrossingDenominatorFloorSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoStepTerminalCrossingDenominatorFloorSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoStepTerminalCrossingDenominatorFloorSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The one-link Wilson crossing ratio is uniformly trapped between
exp (-2 beta) and exp (2 beta), independently of the group elements. -/
theorem specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta g h /
        specialUnitaryWilsonRelativeKernel N beta g k ∈
      Set.Icc (Real.exp (-2 * beta)) (Real.exp (2 * beta)) := by
  have hh :=
    specialUnitaryWilsonRelativeKernel_mem_Icc hN hbeta g h
  have hk :=
    specialUnitaryWilsonRelativeKernel_mem_Icc hN hbeta g k
  have hkPos :
      0 < specialUnitaryWilsonRelativeKernel N beta g k :=
    specialUnitaryWilsonRelativeKernel_pos hN hbeta g k
  constructor
  · apply (le_div_iff₀ hkPos).2
    calc
      Real.exp (-2 * beta) *
          specialUnitaryWilsonRelativeKernel N beta g k ≤
        Real.exp (-2 * beta) * 1 :=
          mul_le_mul_of_nonneg_left hk.2 (Real.exp_nonneg _)
      _ = Real.exp (-2 * beta) := by ring
      _ ≤ specialUnitaryWilsonRelativeKernel N beta g h := hh.1
  · apply (div_le_iff₀ hkPos).2
    calc
      specialUnitaryWilsonRelativeKernel N beta g h ≤ 1 := hh.2
      _ = Real.exp (2 * beta) * Real.exp (-2 * beta) := by
        rw [← Real.exp_add]
        ring_nf
        simp
      _ ≤
        Real.exp (2 * beta) *
          specialUnitaryWilsonRelativeKernel N beta g k :=
            mul_le_mul_of_nonneg_left hk.1 (Real.exp_nonneg _)

/-- Under any continuous ground-state left kernel-section probability law, the
source crossing-ratio expectation inherits the same explicit lower floor
exp (-2 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_crossingRatio_integral_ge_exp_neg_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-2 * beta) ≤
      ∫ A,
        specialUnitaryWilsonRelativeKernel N beta (A source) h /
          specialUnitaryWilsonRelativeKernel N beta (A source) k
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C
  let r :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k
  letI : IsProbabilityMeasure nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C
  have hNumContinuous :
      Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          specialUnitaryWilsonRelativeKernel N beta (A source) h) :=
    (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂
      (continuous_apply source) continuous_const
  have hDenContinuous :
      Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          specialUnitaryWilsonRelativeKernel N beta (A source) k) :=
    (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂
      (continuous_apply source) continuous_const
  have hRContinuous : Continuous r := by
    exact hNumContinuous.div hDenContinuous
      (fun A =>
        ne_of_gt
          (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) k))
  have hRIntegrable : Integrable r nu := by
    refine Integrable.of_bound hRContinuous.aestronglyMeasurable
      (Real.exp (2 * beta)) ?_
    filter_upwards [] with A
    rw [Real.norm_eq_abs, abs_of_pos
      (div_pos
        (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) h)
        (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) k))]
    exact
      (specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
        N hN beta hbeta (A source) h k).2
  have hConst :
      Integrable
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            Real.exp (-2 * beta))
        nu :=
    integrable_const _
  have hMono :
      (∫ _A :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          Real.exp (-2 * beta) ∂nu) ≤
        ∫ A, r A ∂nu := by
    apply integral_mono hConst hRIntegrable
    intro A
    exact
      (specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
        N hN beta hbeta (A source) h k).1
  simpa [nu, r] using hMono

/-- The terminal crossing expectation therefore has the same explicit
volume-independent floor after commuting distinct target/source right updates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalCrossingExpectation_ge_exp_neg_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-2 * beta) ≤
      ∫ A,
        specialUnitaryWilsonRelativeKernel N beta (A source) h /
          specialUnitaryWilsonRelativeKernel N beta (A source) k
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_crossingRatio_integral_ge_exp_neg_two
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
      source h k

/-- Consequently the exact two-step terminal response is bounded by
exp (2 beta) times the absolute covariance in the normal form.

The denominator is no longer an obstruction. The only remaining analytic
quantity is the spatial covariance itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_le_exp_two_mul_abs_covariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      Real.exp (2 * beta) *
        |realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h /
              specialUnitaryWilsonRelativeKernel N beta (A source) k)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
            H N hN beta hbeta B target source g₁ g₂ k)| := by
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let crossing :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k
  let terminalObservable :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
      H N hN beta hbeta B target source g₁ g₂ k
  let covariance := realIntegralCovariance nu crossing terminalObservable
  let mean := ∫ A, crossing A ∂nu
  have hEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k =
        |covariance| / mean := by
    simpa [nu, crossing, terminalObservable, covariance, mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_eq_abs_covariance_div_pos_crossingExpectation
        H N hN beta hbeta B hne g₁ g₂ h k
  have hMeanFloor : Real.exp (-2 * beta) ≤ mean := by
    simpa [nu, crossing, mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalCrossingExpectation_ge_exp_neg_two
        H N hN beta hbeta B target source g₂ h k
  have hMeanPos : 0 < mean :=
    lt_of_lt_of_le (Real.exp_pos (-2 * beta)) hMeanFloor
  have hScale : 1 ≤ Real.exp (2 * beta) * mean := by
    calc
      1 = Real.exp (2 * beta) * Real.exp (-2 * beta) := by
        rw [← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp (2 * beta) * mean :=
        mul_le_mul_of_nonneg_left hMeanFloor (Real.exp_nonneg _)
  rw [hEq]
  apply (div_le_iff₀ hMeanPos).2
  calc
    |covariance| = 1 * |covariance| := by ring
    _ ≤ (Real.exp (2 * beta) * mean) * |covariance| :=
      mul_le_mul_of_nonneg_right hScale (abs_nonneg covariance)
    _ = (Real.exp (2 * beta) * |covariance|) * mean := by ring

end

end MathlibAnalytic
end MGAP4D
