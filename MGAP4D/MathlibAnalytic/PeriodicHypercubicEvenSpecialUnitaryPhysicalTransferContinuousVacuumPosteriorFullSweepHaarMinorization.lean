import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorConditionalHaarMinorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullHaarRefreshSweep
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

/-!
# Posterior full-sweep Haar minorization

PR #5171 proves the literal continuous-vacuum posterior one-link density floor

  exp (-16 * beta) <= p_{B,A,t}(g).

This file upgrades that pointwise statement to an actual measurable posterior
heat-bath kernel, then composes the one-link Haar lower bound through an
arbitrary finite deterministic schedule.  For the canonical schedule which
lists every spatial link exactly once, the resulting sweep dominates the
initial-state-independent full Haar-refresh law with coefficient

  exp (-16 * beta) ^ n,

where `n` is the number of spatial links.

This is strictly a finite-volume Doeblin statement.  The coefficient is
positive at fixed finite volume but is not claimed to be volume-uniform.  No
strict Dobrushin row-sum bound, infinite resolvent, Euclidean-time
identification, H1-D5 exact descent, or complete Yang--Mills mass-gap claim is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance posteriorFullSweepMinorizationTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorFullSweepMinorizationCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorFullSweepMinorizationSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorFullSweepMinorizationMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorFullSweepMinorizationBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorFullSweepMinorizationSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- ENNReal form of the normalized posterior one-link Haar density. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H N hN beta hbeta B A target g)

/-- The normalized posterior one-link density is jointly continuous in the
ambient configuration and inserted gauge value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_prod_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta B z.1 target z.2) := by
  change
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
              H N hN beta hbeta B z.1 target z.2 /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
              H N hN beta hbeta B z.1 target)
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_prod_continuous
      H N hN beta hbeta B target).div
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_continuous
        H N hN beta hbeta B target).comp continuous_fst)
      (fun z =>
        ne_of_gt
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_pos
            H N hN beta hbeta B z.1 target))

/-- The ENNReal posterior one-link density is jointly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity_uncurry_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity
          H N hN beta hbeta B target)) := by
  unfold Function.uncurry
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity
  exact
    ENNReal.measurable_ofReal.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_prod_continuous
        H N hN beta hbeta B target).measurable

/-- The literal tilted posterior one-link law is exactly Haar with the named
normalized ENNReal density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_eq_withDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta B A target =
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).withDensity
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity
          H N hN beta hbeta B target A) := by
  rfl

/-- Measurable gauge-valued posterior one-link conditional kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  Kernel.withDensity
    (Kernel.const
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity
      H N hN beta hbeta B target)

/-- The measurable posterior conditional kernel agrees pointwise with the
literal posterior one-link conditional probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel
        H N hN beta hbeta B target A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta B A target := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel,
    Kernel.withDensity_apply _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity_uncurry_measurable
        H N hN beta hbeta B target),
    Kernel.const_apply]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_eq_withDensity
      H N hN beta hbeta B A target).symm

/-- The measurable posterior one-link conditional kernel is Markov. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel
        H N hN beta hbeta B target) := by
  refine ⟨fun A => ?_⟩
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target

/-- The one-link posterior Haar-minorization coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
    (beta : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-16 * beta))

/-- The literal posterior one-link conditional law dominates normalized Haar
by the sharp floor supplied by PR #5171. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_lower_bound_normalizedCompactHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
        beta •
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let eps : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
      beta
  let p :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity
      H N hN beta hbeta B target A
  have hDensity : (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => eps) ≤ᵐ[μ] p := by
    filter_upwards with g
    dsimp [eps, p,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalENNRealDensity]
    exact
      ENNReal.ofReal_le_ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_exp_neg_sixteen_mul_le
          H N hN beta hbeta B A target g)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_eq_withDensity]
  change eps • μ ≤ μ.withDensity p
  simpa [eps, p, μ] using
    (withDensity_mono (μ := μ) hDensity)

/-- Full-configuration posterior heat-bath kernel: draw the selected link from
its exact posterior conditional law and insert it back into the configuration. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (Kernel.id ×ₖ
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel
        H N hN beta hbeta B target).map
    (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Function.update z.1 target z.2)

/-- Every full-configuration posterior one-link heat-bath update is Markov. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
        H N hN beta hbeta B target) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
  exact
    Kernel.IsMarkovKernel.map
      (Kernel.id ×ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel
          H N hN beta hbeta B target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target)

/-- Pointwise form of the full-configuration posterior heat-bath kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_apply_eq_map_conditionalMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
        H N hN beta hbeta B target A =
      Measure.map
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) := by
  ext s hs
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel,
    Kernel.map_apply' _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target)
      A hs,
    Kernel.id_prod_apply' _ A
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target) hs),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalKernel_apply]
  have hSingle :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hSingle hs]
  rfl

/-- The full-configuration posterior one-link heat-bath kernel dominates the
corresponding independent Haar-refresh kernel by exp(-16 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_lower_bound_haarRefreshKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
        beta •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
        H N target A ≤
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
      H N hN beta hbeta B target A := by
  have hReplace :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target).comp (measurable_const.prodMk measurable_id)
  have hFiber :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_lower_bound_normalizedCompactHaar
      H N hN beta hbeta B A target
  have hMapped :=
    Measure.map_mono hFiber hReplace
  have hMapped' :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
          beta •
        Measure.map
          (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
            Function.update A target g)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      Measure.map
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) := by
    simpa only [Measure.map_smul] using hMapped
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_apply_eq_map_conditionalMeasure]
  exact hMapped'

/-- Ordered composition of exact posterior one-link heat-bath updates.  The
head target is updated first. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    List (PeriodicHypercubicEvenSpatialSliceLink H) →
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  | [] => Kernel.id
  | target :: targets =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
          H N hN beta hbeta B target

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_nil
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
        H N hN beta hbeta B [] = Kernel.id := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_cons
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (targets : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
        H N hN beta hbeta B (target :: targets) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
          H N hN beta hbeta B target := by
  rfl

/-- Every finite exact posterior deterministic schedule is Markov. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (targets : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
        H N hN beta hbeta B targets) := by
  induction targets with
  | nil =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_nil]
      infer_instance
  | cons target targets ih =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_cons]
      letI : IsMarkovKernel
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
            H N hN beta hbeta B targets) := ih
      infer_instance

/-- Every finite exact posterior schedule dominates the corresponding
independent Haar-refresh schedule, with one factor exp(-16 beta) per update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_lower_bound_haarRefreshSchedule
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (targets : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
        beta) ^ targets.length •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N targets A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
        H N hN beta hbeta B targets A := by
  induction targets generalizing A with
  | nil =>
      simp
  | cons target targets ih =>
      let eps : ℝ≥0∞ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
          beta
      let Rhead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
          H N target
      let Khead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
          H N hN beta hbeta B target
      let Rtail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N targets
      let Ktail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
          H N hN beta hbeta B targets
      have hHead : eps • Rhead A ≤ Khead A := by
        dsimp [eps, Rhead, Khead]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_lower_bound_haarRefreshKernel
            H N hN beta hbeta B target A
      have hTail :
          ∀ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            eps ^ targets.length • Rtail C ≤ Ktail C := by
        intro C
        dsimp [eps, Rtail, Ktail]
        exact ih C
      have hComp :=
        finiteMarkovKernel_comp_measure_minorization
          Khead Ktail Rhead Rtail eps (eps ^ targets.length) A hHead hTail
      simpa [
        eps,
        Rhead,
        Khead,
        Rtail,
        Ktail,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_cons,
        pow_succ,
        mul_comm,
        mul_left_comm,
        mul_assoc] using hComp

/-- One complete deterministic posterior sweep through every spatial link
dominates a common initial-state-independent full Haar-refresh law.

The coefficient is exactly exp(-16 beta)^n with n the finite number of spatial
links encoded by the canonical all-link schedule. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorFullDeterministicSweep_lower_bound_commonHaarRefresh
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
        beta) ^
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) A := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorDeterministicScheduleKernel_lower_bound_haarRefreshSchedule
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H) A
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshSweep_apply_eq_measure]
    at h
  exact h

end

end MathlibAnalytic
end MGAP4D
