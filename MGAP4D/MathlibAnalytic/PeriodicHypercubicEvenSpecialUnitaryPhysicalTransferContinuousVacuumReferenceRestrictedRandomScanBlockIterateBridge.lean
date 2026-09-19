import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanDoeblinStationaryBlockLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanIterate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance referenceRestrictedRandomScanBlockIterateBridgeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanBlockIterateBridgeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanBlockIterateBridgeSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanBlockIterateBridgeSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanBlockIterateBridgeSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanBlockIterateBridgeSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The original observable-level restricted random-scan step is exactly
integration against the normalized restricted random-scan Markov kernel.

The boundedness hypothesis is used only to justify the finite Bochner-integral
distribution over the normalized finite sum of one-link kernels. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_eq_integral_restrictedRandomScanKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (_hM : 0 ≤ M)
    (hBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X| ≤ M)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k A f =
      ∫ X, f X ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
          H N hN beta hbeta B target source k g₂ A := by
  classical
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_apply]
  rw [integral_smul_measure]
  rw [integral_finset_sum_measure (fun fiber _ => by
    let μ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A
    letI : IsProbabilityMeasure μ := by
      dsimp [μ]
      infer_instance
    refine Integrable.of_bound hf.aestronglyMeasurable M ?_
    exact Filter.Eventually.of_forall fun X => by
      simpa [Real.norm_eq_abs] using hBound X)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_nil]
  simp [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- Uniform absolute boundedness is preserved by every original observable-level
restricted random-scan iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_abs_le_of_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X| ≤ M) :
    ∀ (n : ℕ)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f n A| ≤ M := by
  intro n
  induction n with
  | zero =>
      intro A
      simpa using hBound A
  | succ n ih =>
      intro A
      let fn :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f n
      let μ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
          H N hN beta hbeta B target source k g₂ A
      have hfnStrong : StronglyMeasurable fn := by
        dsimp [fn]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k f hf n
      have hfnBound :
          ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            |fn X| ≤ M := by
        intro X
        exact ih X
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_eq_integral_restrictedRandomScanKernel
          H N hN beta hbeta B target source g₂ k fn hfnStrong M hM hfnBound A
      letI : IsProbabilityMeasure μ := by
        dsimp [μ]
        infer_instance
      have hfnInt : Integrable fn μ := by
        refine Integrable.of_bound hfnStrong.aestronglyMeasurable M ?_
        exact Filter.Eventually.of_forall fun X => by
          simpa [Real.norm_eq_abs] using hfnBound X
      have hAbsInt : Integrable (fun X => |fn X|) μ := by
        simpa [Real.norm_eq_abs] using hfnInt.norm
      have hConstInt :
          Integrable
            (fun _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => M)
            μ :=
        integrable_const M
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      change
        |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
            H N hN beta hbeta B target source g₂ k A fn| ≤ M
      rw [hStep]
      change |∫ X, fn X ∂μ| ≤ M
      calc
        |∫ X, fn X ∂μ| ≤ ∫ X, |fn X| ∂μ :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N, M ∂μ := by
          apply integral_mono hAbsInt hConstInt
          intro X
          exact hfnBound X
        _ = M := by simp

/-- Integrating an observable against the n-step restricted random-scan block
kernel is exactly the original observable-level n-step random-scan iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_integral_eq_expectationIterate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X| ≤ M) :
    ∀ (n : ℕ)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      (∫ X, f X ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂ n A) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f n A := by
  intro n
  induction n with
  | zero =>
      intro A
      simp
  | succ n ih =>
      intro A
      let K :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂ n
      let Q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
          H N hN beta hbeta B target source k g₂
      let fn :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f n
      have hCompInt : Integrable f ((K ∘ₖ Q) A) := by
        letI : IsProbabilityMeasure ((K ∘ₖ Q) A) := by infer_instance
        refine Integrable.of_bound hf.aestronglyMeasurable M ?_
        exact Filter.Eventually.of_forall fun X => by
          simpa [Real.norm_eq_abs] using hBound X
      have hFubini :=
        ProbabilityTheory.Kernel.integral_comp
          (η := K) (κ := Q) (a := A) hCompInt
      have hfnStrong : StronglyMeasurable fn := by
        dsimp [fn]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k f hf n
      have hfnBound :
          ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            |fn X| ≤ M := by
        intro X
        dsimp [fn]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_abs_le_of_abs_le
            H N hN beta hbeta B target source g₂ k f hf M hM hBound n X
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_eq_integral_restrictedRandomScanKernel
          H N hN beta hbeta B target source g₂ k fn hfnStrong M hM hfnBound A
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_succ]
      change (∫ X, f X ∂(K ∘ₖ Q) A) = _
      calc
        (∫ X, f X ∂(K ∘ₖ Q) A) =
            ∫ C, (∫ X, f X ∂K C) ∂Q A := by
              simpa using hFubini
        _ = ∫ C, fn C ∂Q A := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun C => by
            dsimp [fn]
            exact ih C
        _ =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
              H N hN beta hbeta B target source g₂ k A fn := hStep.symm
        _ =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k f (n + 1) A := by
              rfl

/-- Additivity of the original observable-level random-scan iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f m) n =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k f (m + n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      rw [ih]

/-- One complete-length kernel block is exactly the original random-scan
observable iterate at the complete-schedule length. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation_eq_expectationIterate_scheduleLength
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X| ≤ M)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
        H N hN beta hbeta B target source k g₂ f A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_integral_eq_expectationIterate
      H N hN beta hbeta B target source k g₂ f hf M hM hBound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length A

/-- Exact bridge from complete-block observable iteration to the original
one-step restricted random-scan observable iteration.

For L equal to the complete spatial-link schedule length,
  P_block^n f = P_scan^(n * L) f
pointwise at every finite volume. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_eq_expectationIterate_mul_scheduleLength
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X - f Y| ≤ R) :
    ∀ (n : ℕ)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B target source k g₂ f n A =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length) A := by
  let A₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun _ => 1
  let M : ℝ := R + |f A₀|
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg hR (abs_nonneg _)
  have hBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X| ≤ M := by
    intro X
    dsimp [M]
    calc
      |f X| = |(f X - f A₀) + f A₀| := by
        congr 1
        ring
      _ ≤ |f X - f A₀| + |f A₀| := abs_add_le _ _
      _ ≤ R + |f A₀| := by
        exact add_le_add_right (hOsc X A₀) _
  intro n
  induction n with
  | zero =>
      intro A
      simp
  | succ n ih =>
      intro A
      let L :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length
      let m := n * L
      let oldn :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k f m
      have hFnEq :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
              H N hN beta hbeta B target source k g₂ f n =
            oldn := by
        funext C
        dsimp [oldn, m, L]
        exact ih C
      have hOldStrong : StronglyMeasurable oldn := by
        dsimp [oldn, m]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k f hf (n * L)
      have hOldBound :
          ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            |oldn X| ≤ M := by
        intro X
        dsimp [oldn, m]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_abs_le_of_abs_le
            H N hN beta hbeta B target source g₂ k f hf M hM hBound (n * L) X
      change
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
            H N hN beta hbeta B target source k g₂
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
              H N hN beta hbeta B target source k g₂ f n) A =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k f ((n + 1) * L) A
      rw [hFnEq]
      calc
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
            H N hN beta hbeta B target source k g₂ oldn A =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k oldn L A := by
              dsimp [L]
              exact
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation_eq_expectationIterate_scheduleLength
                  H N hN beta hbeta B target source k g₂ oldn hOldStrong M hM hOldBound A
        _ =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k f (m + L) A := by
              exact congrFun
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_add
                  H N hN beta hbeta B target source g₂ k f m L) A
        _ =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k f ((n + 1) * L) A := by
              simp [m, Nat.succ_mul]

end

end MathlibAnalytic
end MGAP4D
