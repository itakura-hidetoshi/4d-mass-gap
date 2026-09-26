import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance
import Mathlib.Tactic

/-!
# Background-update Harnack comparison for conditional variance

PR #4472 proves the bounded-test consequence of a stronger fact used
internally in its proof: when one background link is changed away from the
resampled fiber, the two normalized physical one-link laws mutually dominate
one another by the normalized Harnack factor

  K(beta) = (exp (32 beta))^2.

This file exposes that measure-level statement and applies it directly to
extended variance.

The generic variance step is sharp with respect to measure domination:
if probability measures satisfy

  mu <= K * nu,

then every L2 variable under mu satisfies

  evariance_mu(X) <= K * evariance_nu(X).

The proof uses the new-law mean as an admissible center for the old law, then
applies measure monotonicity to the nonnegative squared residual.  No triangle
inequality and no factor two are introduced.

This is the comparison needed for the sole remaining old-target-law variance
term after PR #4785.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backgroundUpdateVarianceComparisonSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backgroundUpdateVarianceComparisonSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backgroundUpdateVarianceComparisonSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backgroundUpdateVarianceComparisonSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backgroundUpdateVarianceComparisonSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Sharp generic variance comparison from one-sided measure domination.

The old variance chooses its own optimal scalar center, so it is no larger
than the old-law residual around the new-law mean.  The latter transports
through the measure inequality with exactly the same scalar factor. -/
theorem evariance_le_mul_of_measure_le_smul
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℝ≥0∞)
    (hμν : μ ≤ K • ν)
    (X : α → ℝ)
    (hXμ : MemLp X 2 μ) :
    evariance X μ ≤ K * evariance X ν := by
  let c : ℝ := ∫ x, X x ∂ν
  calc
    evariance X μ ≤ doobCenteredSquaredResidual μ X c :=
      evariance_le_doobCenteredSquaredResidual μ X hXμ c
    _ = ∫⁻ x, ENNReal.ofReal ((X x - c) ^ 2) ∂μ := by
      rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal ((X x - c) ^ 2) ∂(K • ν) :=
      lintegral_mono' hμν le_rfl
    _ = K * ∫⁻ x, ENNReal.ofReal ((X x - c) ^ 2) ∂ν := by
      simpa [smul_eq_mul] using
        (lintegral_smul_measure
          (μ := ν) K (fun x => ENNReal.ofReal ((X x - c) ^ 2)))
    _ = K * evariance X ν := by
      unfold c
      rw [evariance_eq_lintegral_ofReal]

/-- The actual normalized physical one-link laws at two backgrounds differing
at one off-fiber link mutually dominate one another by the normalized Harnack
factor (exp (32 beta))^2.

This is exactly the measure-level fact already used internally by PR #4472;
it is exposed here because variance comparison needs the measure inequality
itself rather than only its bounded-test corollary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_pairwise_le_harnackLawFactor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber ≠ backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
        (Function.update A backgroundFiber u) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber v) ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
        (Function.update A backgroundFiber v) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber u) := by
  classical
  let μHaar : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber u
  let Av : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber v
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Au fiber
  let vWeight : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Av fiber
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (32 * beta))
  let K : ℝ := (Real.exp (32 * beta)) ^ 2
  let μu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  let μv : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  have hComm :
      ∀ (z x : Matrix.specialUnitaryGroup (Fin N) ℂ),
        Function.update (Function.update A backgroundFiber z) fiber x =
          Function.update (Function.update A fiber x) backgroundFiber z := by
    intro z x
    funext e
    by_cases hef : e = fiber
    · subst e
      simp [hDistinct]
    · by_cases heb : e = backgroundFiber
      · subst e
        simp [hef]
      · simp [hef, heb]
  have hwv : ∀ x, w x ≤ R * vWeight x := by
    intro x
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B distinguishedTarget distinguishedSource backgroundFiber
        k g₂ (Function.update A fiber x) u v).1
    have hReal' :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Au fiber x) ≤
          Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Av fiber x) := by
      rw [hComm u x, hComm v x]
      exact hReal
    dsimp [w, vWeight, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Au fiber x)) ≤
        ENNReal.ofReal
          (Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Av fiber x)) :=
        ENNReal.ofReal_le_ofReal hReal'
      _ =
        ENNReal.ofReal (Real.exp (32 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Av fiber x)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hvw : ∀ x, vWeight x ≤ R * w x := by
    intro x
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B distinguishedTarget distinguishedSource backgroundFiber
        k g₂ (Function.update A fiber x) u v).2
    have hReal' :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Av fiber x) ≤
          Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Au fiber x) := by
      rw [hComm v x, hComm u x]
      exact hReal
    dsimp [w, vWeight, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Av fiber x)) ≤
        ENNReal.ofReal
          (Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Au fiber x)) :=
        ENNReal.ofReal_le_ofReal hReal'
      _ =
        ENNReal.ofReal (Real.exp (32 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Au fiber x)) := by
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
      μHaar w vWeight R hR0 hRtop hwv hvw
  have hScalar : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    ring
  rw [hScalar] at hPair
  have hLawU : μu = doobWeightedMeasure μHaar w := by
    dsimp [μu, μHaar, w]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure]
    rfl
  have hLawV : μv = doobWeightedMeasure μHaar vWeight := by
    dsimp [μv, μHaar, vWeight]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure]
    rfl
  have hμν : μu ≤ ENNReal.ofReal K • μv := by
    rw [hLawU, hLawV]
    exact hPair.1
  have hνμ : μv ≤ ENNReal.ofReal K • μu := by
    rw [hLawU, hLawV]
    exact hPair.2
  simpa [μu, μv, K] using And.intro hμν hνμ

/-- Background-update Harnack comparison for extended variance of any variable
that is L2 under the old fiber law.

The coefficient is exactly the normalized law-domination factor already
present in PR #4472. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_evariance_le_harnackLawFactor_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber ≠ backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX :
      MemLp X 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber u))) :
    evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber u)) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        evariance X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
            (Function.update A backgroundFiber v)) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber u)
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber v)
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber u)
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
      (Function.update A backgroundFiber v)
  have hPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_pairwise_le_harnackLawFactor
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber backgroundFiber
      hDistinct k g₂ u v A
  have hDom : μ ≤ ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) • ν := by
    simpa [μ, ν] using hPair.1
  have hX' : MemLp X 2 μ := by
    simpa [μ] using hX
  simpa [μ, ν] using
    evariance_le_mul_of_measure_le_smul
      μ ν (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)) hDom X hX'

end

end MGAP4D.MathlibAnalytic
