import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionContinuousDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetKernelHarnack
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasurePairwiseComparison
import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import Mathlib.Tactic

/-!
# Fixed-right kernel-section Harnack comparison

Changing one fixed right-boundary link changes the one-slab kernel pointwise by
at most the already-proved factor `exp (8 * beta)`.  The left vacuum factor in
a fixed-right kernel-section weight is unchanged, so the same pointwise
comparison holds for the complete continuous kernel-section weight.

After normalization this costs one further Harnack factor.  Hence the two
fixed-right kernel-section probability laws are mutually dominated with
constant `(exp (8 * beta))^2`, and every strongly measurable test bounded by
one changes by at most

  2 * (((exp (8 * beta))^2 - 1) / ((exp (8 * beta))^2 + 1)).

This coefficient vanishes at beta = 0 and is volume-independent.  No response
closure, covariance decay, sweep contraction, coercivity, or mass-gap input is
used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Normalized-law Harnack influence for one fixed right-boundary update. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
    (beta : ℝ) : ℝ :=
  let K := (Real.exp (8 * beta)) ^ 2
  2 * ((K - 1) / (K + 1))

/-- The fixed-right boundary-update Harnack influence is nonnegative at
nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
        beta := by
  let x : ℝ := Real.exp (8 * beta)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  have hK : 1 ≤ x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
  change 0 ≤ 2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
    ((Real.exp (8 * beta)) ^ 2 + 1))
  exact
    mul_nonneg (by norm_num)
      (div_nonneg
        (sub_nonneg.mpr (by simpa [x] using hK))
        (by positivity))

/-- The continuous fixed-right kernel-section weights inherit the exact
pointwise `exp (8 * beta)` pairwise Harnack comparison from the one-slab
kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_update_right_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta (Function.update C source h) A ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
            H N hN beta hbeta (Function.update C source k) A ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta (Function.update C source k) A ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
            H N hN beta hbeta (Function.update C source h) A := by
  have hOmega :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta A :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta A).le
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_pairwise_harnack
      H N hN beta hbeta A C source h k
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  constructor
  · calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (Function.update C source h) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta A *
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update C source k)) :=
        mul_le_mul_of_nonneg_left hKernel.1 hOmega
      _ =
        Real.exp (8 * beta) *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update C source k)) := by
        ring
  · calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (Function.update C source k) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta A *
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update C source h)) :=
        mul_le_mul_of_nonneg_left hKernel.2 hOmega
      _ =
        Real.exp (8 * beta) *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update C source h)) := by
        ring

/-- Updating one fixed right-boundary link changes expectations under the
normalized continuous kernel-section law by at most the volume-independent
boundary-update Harnack influence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_update_right_boundedTest_difference_le_harnackInfluence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ A, |phi A| ≤ 1) :
    |(∫ A, phi A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update C source h)) -
      (∫ A, phi A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update C source k))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
        beta := by
  let μHaar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let wh : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta (Function.update C source h) A)
  let wk : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta (Function.update C source k) A)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  let K : ℝ := (Real.exp (8 * beta)) ^ 2
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta (Function.update C source h)
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta (Function.update C source k)
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta (Function.update C source h)
  letI : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta (Function.update C source k)
  have hwk : ∀ A, wh A ≤ R * wk A := by
    intro A
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_update_right_pairwise_harnack
        H N hN beta hbeta C source h k A).1
    dsimp [wh, wk, R]
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
            H N hN beta hbeta (Function.update C source h) A) ≤
        ENNReal.ofReal
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source k) A) :=
        ENNReal.ofReal_le_ofReal hReal
      _ =
        ENNReal.ofReal (Real.exp (8 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source k) A) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hkw : ∀ A, wk A ≤ R * wh A := by
    intro A
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_update_right_pairwise_harnack
        H N hN beta hbeta C source h k A).2
    dsimp [wh, wk, R]
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
            H N hN beta hbeta (Function.update C source k) A) ≤
        ENNReal.ofReal
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source h) A) :=
        ENNReal.ofReal_le_ofReal hReal
      _ =
        ENNReal.ofReal (Real.exp (8 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source h) A) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hR0 : R ≠ 0 := by
    exact ne_of_gt (by
      dsimp [R]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hPair :=
    doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
      μHaar wh wk R hR0 hRtop hwk hkw
  have hScalar : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    ring
  rw [hScalar] at hPair
  have hLawH : μh = doobWeightedMeasure μHaar wh := by
    rfl
  have hLawK : μk = doobWeightedMeasure μHaar wk := by
    rfl
  have hμν : μh ≤ ENNReal.ofReal K • μk := by
    rw [hLawH, hLawK]
    exact hPair.1
  have hνμ : μk ≤ ENNReal.ofReal K • μh := by
    rw [hLawH, hLawK]
    exact hPair.2
  have hExp : 1 ≤ Real.exp (8 * beta) :=
    Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg (Real.exp (8 * beta) - 1)]
  have hBound :=
    probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
      μh μk K hK hμν hνμ phi hphi hphiBound
  simpa [
    μh, μk, K,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence] using
    hBound

end

end MathlibAnalytic
end MGAP4D
