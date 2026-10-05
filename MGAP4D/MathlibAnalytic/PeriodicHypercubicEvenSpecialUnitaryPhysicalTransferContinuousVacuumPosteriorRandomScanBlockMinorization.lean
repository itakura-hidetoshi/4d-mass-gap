import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFullSweepHaarMinorization
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

/-!
# Posterior random-scan block Haar minorization

The previous posterior full-sweep theorem gives the deterministic factor

  eps^n,  eps = exp (-16 * beta).

This file realizes the uniform posterior random scan as the normalized finite
sum of exact one-link posterior heat-bath kernels.  A prescribed ordered sweep
appears in an n-step random-scan block with factor q^n, where q = 1/n.
Combining the two gives the fixed-volume Doeblin coefficient

  delta = (q * eps)^n = n^(-n) * exp (-16 * beta * n)

in ENNReal form.

No volume-uniform lower bound is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance posteriorRandomScanBlockSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorRandomScanBlockTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRandomScanBlockCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRandomScanBlockSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRandomScanBlockMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRandomScanBlockBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact uniform selection coefficient on the finite spatial-link carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
    (H : ℕ) : ℝ≥0∞ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞)⁻¹

/-- Unnormalized finite sum of all exact posterior one-link heat-bath kernels. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernelSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Kernel.sum fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
      H N hN beta hbeta B target

/-- The finite sum of posterior one-link kernels is s-finite. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernelSum_isSFiniteKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsSFiniteKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernelSum
        H N hN beta hbeta B) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernelSum
  rw [Kernel.sum_fintype]
  exact
    Kernel.IsSFiniteKernel.finset_sum Finset.univ (by
      intro target _
      infer_instance)

/-- Uniform exact posterior random-scan Markov kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Kernel.withDensity
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernelSum
      H N hN beta hbeta B)
    (fun _ _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
        H)

/-- Pointwise measure formula for the posterior random-scan kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
        H N hN beta hbeta B A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
          H •
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
            H N hN beta hbeta B target A) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernelSum
  rw [Kernel.withDensity_apply _ measurable_const]
  rw [withDensity_const]
  rw [Kernel.sum_fintype]
  rw [Kernel.finset_sum_apply]

/-- The exact posterior random-scan kernel is Markov. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
        H N hN beta hbeta B) := by
  refine ⟨fun A => ⟨?_⟩⟩
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_apply]
  have hCardPos :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H))
  have hCardNe :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCardPos
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
  simp only [Measure.smul_apply, MeasurableSet.univ,
    Finset.sum_apply, Measure.finset_sum_apply, measure_univ]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hCardNe (by simp)

/-- Every selected posterior one-link update occurs in the uniform random scan
with exactly the coefficient 1/n. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_lower_bound_selectedOneLink
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
        H •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
        H N hN beta hbeta B target A ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
      H N hN beta hbeta B A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_apply]
  apply Measure.le_iff.2
  intro s hs
  simp only [Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  apply mul_le_mul_left'
  exact
    Finset.single_le_sum
      (fun e _ =>
        zero_le
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
            H N hN beta hbeta B e A s))
      (Finset.mem_univ target)

/-- Iteration of the exact posterior random-scan kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ℕ →
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  | 0 => Kernel.id
  | n + 1 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B n ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
          H N hN beta hbeta B

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B 0 = Kernel.id := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B (n + 1) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B n ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
          H N hN beta hbeta B := by
  rfl

/-- Every finite posterior random-scan block is Markov. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (n : ℕ) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B n) := by
  induction n with
  | zero =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_zero]
      infer_instance
  | succ n ih =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_succ]
      letI : IsMarkovKernel
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
            H N hN beta hbeta B n) := ih
      infer_instance

/-- A prescribed deterministic posterior schedule appears inside an
equal-length uniform random-scan block with exact selection factor q^length. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_lower_bound_deterministicSchedule
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (targets : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
        H) ^ targets.length •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
        H N hN beta hbeta B targets A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B targets.length A := by
  induction targets generalizing A with
  | nil =>
      simp
  | cons target targets ih =>
      let q : ℝ≥0∞ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
          H
      let Rhead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
          H N hN beta hbeta B target
      let Khead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
          H N hN beta hbeta B
      let Rtail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets
      let Ktail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B targets.length
      have hHead : q • Rhead A ≤ Khead A := by
        dsimp [q, Rhead, Khead]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_lower_bound_selectedOneLink
            H N hN beta hbeta B target A
      have hTail :
          ∀ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            q ^ targets.length • Rtail C ≤ Ktail C := by
        intro C
        dsimp [q, Rtail, Ktail]
        exact ih C
      have hComp :=
        finiteMarkovKernel_comp_measure_minorization
          Khead Ktail Rhead Rtail q (q ^ targets.length) A hHead hTail
      simpa [
        q,
        Rhead,
        Khead,
        Rtail,
        Ktail,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_cons,
        pow_succ,
        mul_comm,
        mul_left_comm,
        mul_assoc] using hComp

/-- The canonical all-spatial-link schedule has length exactly the finite
cardinality of the spatial-link carrier. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule_length
    (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length =
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule]

/-- Fixed-volume posterior block Doeblin coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
    (H : ℕ)
    (beta : ℝ) : ℝ≥0∞ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
      H *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
      beta) ^
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length

/-- Explicit cardinality form of the posterior block Doeblin coefficient:
(1/n * exp(-16 beta))^n. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient_eq
    (H : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
        H beta =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (Real.exp (-16 * beta))) ^
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient]

/-- A complete-length posterior random-scan block dominates the common full
Haar-refresh law.  This is the finite-volume block Doeblin inequality required
for oscillation contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlock_lower_bound_commonHaarRefresh
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
        H beta •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
  let targets :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H
  let q : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
      H
  let eps : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
      beta
  have hSweep :
      eps ^ targets.length •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
          H N ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets A := by
    dsimp [eps, targets]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorFullDeterministicSweep_lower_bound_commonHaarRefresh
        H N hN beta hbeta B A
  have hBlock :
      q ^ targets.length •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets A ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B targets.length A := by
    dsimp [q, targets]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_lower_bound_deterministicSchedule
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) A
  have hScaled :
      q ^ targets.length •
          (eps ^ targets.length •
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
              H N) ≤
        q ^ targets.length •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
            H N hN beta hbeta B targets A := by
    apply Measure.le_iff.2
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact
      mul_le_mul_left'
        (Measure.le_iff.1 hSweep s hs)
        (q ^ targets.length)
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
          H beta •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
          H N =
      q ^ targets.length •
        (eps ^ targets.length •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
            H N) := by
          simp [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient,
            targets,
            q,
            eps,
            mul_pow,
            smul_smul]
    _ ≤
      q ^ targets.length •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets A := hScaled
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B targets.length A := hBlock
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
            rfl

end

end MathlibAnalytic
end MGAP4D
