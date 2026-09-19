import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanKernel
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceRestrictedRandomScanBlockMinorizationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanBlockMinorizationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanBlockMinorizationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanBlockMinorizationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanBlockMinorizationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanBlockMinorizationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual restricted random-scan kernel iterated for a fixed finite number
of steps.  The successor orientation matches the deterministic schedule
convention: one random-scan update is performed first, then the remaining
block. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ℕ →
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  | 0 => Kernel.id
  | n + 1 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂ n ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
          H N hN beta hbeta B target source k g₂

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂ 0 = Kernel.id := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂ (n + 1) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂ n ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
          H N hN beta hbeta B target source k g₂ := by
  rfl

/-- Every finite actual restricted random-scan block is a Markov kernel. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂ n) := by
  induction n with
  | zero =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_zero]
      infer_instance
  | succ n ih =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_succ]
      letI : IsMarkovKernel
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
            H N hN beta hbeta B target source k g₂ n) := ih
      infer_instance

/-- Every finite actual restricted random-scan block preserves the normalized
continuous-vacuum reference probability law exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_comp_referenceProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂ n ∘ₘ
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_succ,
        ← Measure.comp_assoc,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_comp_referenceProbabilityMeasure]
      exact ih

/-- A prescribed ordered deterministic schedule occurs inside an actual
restricted random-scan block with the exact product of the uniform one-step
selection coefficients.

This is a fixed-finite-volume kernel-order statement.  It does not use
terminal covariance decay, remote-residual smallness, a sweep contraction, or
any downstream mass-gap input. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_lower_bound_deterministicSchedule
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
        H) ^ fibers.length •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
        H N hN beta hbeta B target source k g₂ fibers A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂ fibers.length A := by
  induction fibers generalizing A with
  | nil =>
      simp
  | cons fiber fibers ih =>
      let q : ℝ≥0∞ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
          H
      let Rhead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂
      let Khead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel
          H N hN beta hbeta B target source k g₂
      let Rtail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
          H N hN beta hbeta B target source k g₂ fibers
      let Ktail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂ fibers.length
      have hHead : q • Rhead A ≤ Khead A := by
        dsimp [q, Rhead, Khead]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanKernel_lower_bound_selectedOneLink
            H N hN beta hbeta B target source fiber k g₂ A
      have hTail :
          ∀ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            q ^ fibers.length • Rtail C ≤ Ktail C := by
        intro C
        dsimp [q, Rtail, Ktail]
        exact ih C
      have hComp :=
        finiteMarkovKernel_comp_measure_minorization
          Khead Ktail Rhead Rtail q (q ^ fibers.length) A hHead hTail
      simpa [
        q,
        Rhead,
        Khead,
        Rtail,
        Ktail,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel_cons,
        pow_succ,
        mul_comm,
        mul_left_comm,
        mul_assoc] using hComp

/-- The fixed-volume Doeblin coefficient obtained by forcing one prescribed
complete sweep inside a random-scan block and using the one-link Haar
minorization along that sweep. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
    (H : ℕ)
    (beta : ℝ) : ℝ≥0∞ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
      H *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient
      beta) ^
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length

/-- One complete-length actual restricted random-scan block dominates the same
initial-state-independent Haar-refresh law as a deterministic full sweep.

The coefficient is exactly the product of the prescribed-schedule selection
probability and the deterministic-sweep Haar minorization.  It may decay with
finite volume; only strict fixed-volume positivity is needed by the subsequent
ergodic closure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlock_lower_bound_commonHaarRefresh
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
        H beta •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
  let fibers :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H
  let q : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanCoefficient
      H
  let eps : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient
      beta
  have hSweep :
      eps ^ fibers.length •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
          H N ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
          H N hN beta hbeta B target source k g₂ fibers A := by
    dsimp [eps, fibers]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullDeterministicSweep_lower_bound_commonHaarRefresh
        H N hN beta hbeta B target source k g₂ A
  have hBlock :
      q ^ fibers.length •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
          H N hN beta hbeta B target source k g₂ fibers A ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂ fibers.length A := by
    dsimp [q, fibers]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_lower_bound_deterministicSchedule
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) A
  have hScaled :
      q ^ fibers.length •
          (eps ^ fibers.length •
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
              H N) ≤
        q ^ fibers.length •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
            H N hN beta hbeta B target source k g₂ fibers A := by
    apply Measure.le_iff.2
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact
      mul_le_mul_left'
        (Measure.le_iff.1 hSweep s hs)
        (q ^ fibers.length)
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
          H beta •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
          H N =
      q ^ fibers.length •
        (eps ^ fibers.length •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
            H N) := by
          simp [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient,
            fibers,
            q,
            eps,
            mul_pow,
            smul_smul]
    _ ≤
      q ^ fibers.length •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
          H N hN beta hbeta B target source k g₂ fibers A := hScaled
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂ fibers.length A := hBlock
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
            rfl

end

end MathlibAnalytic
end MGAP4D
