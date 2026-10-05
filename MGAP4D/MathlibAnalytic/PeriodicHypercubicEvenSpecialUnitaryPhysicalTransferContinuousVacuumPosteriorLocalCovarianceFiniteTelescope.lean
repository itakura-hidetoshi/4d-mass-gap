import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorResponseCovarianceBridge
import Mathlib.Tactic

/-!
# Finite posterior local-covariance telescope

The remote-response bridge of PR #5166 reduces the ordinary posterior response
to a covariance of two one-coordinate local factors.  The source local factor
has a special advantage: under a one-link posterior conditional expectation at
any different coordinate it is exactly fiber-constant.

This file exploits that locality directly, without introducing a separate
abstract self-adjointness theorem.

For L_s the source-local factor and O a bounded continuous observable:

* if e != s, the covariance defect
    Cov(L_s,O) - Cov(L_s,Q_e O)
  is exactly zero;
* if e = s, its absolute value is bounded by
    (width(beta)/2) * variation_O(s),
  where width(beta) = exp(8 beta) - exp(-8 beta).

After uniform random-scan averaging and finite iteration this gives

  |Cov(L_s,O) - Cov(L_s,R^M O)|
    <= (width(beta)/2) * w_M(s),

where w_M is exactly the finite non-strict resolvent profile of PR #5165.

For a target-local factor O = F_t this becomes a finite remote-response
bootstrap inequality, with only an explicit terminal covariance remainder
left over.

No strict row-sum hypothesis, infinite resolvent, remainder limit, covariance
decay, posterior fixed point, heat-bath-time / Euclidean-time identification,
H1-D5 exact descent, or complete Yang--Mills mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance posteriorLocalCovarianceTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorLocalCovarianceCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorLocalCovarianceSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorLocalCovarianceMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorLocalCovarianceBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorLocalCovarianceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem posterior_local_covariance_bcf_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    Integrable
      (fun A => O A)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
        H N hN beta hbeta B) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  change Integrable (fun A => O A) mu
  exact
    O.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Posterior mean is additive on bounded-continuous observables. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_add_bcf
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B (F + G) =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B F +
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B G := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  simpa using
    integral_add
      (posterior_local_covariance_bcf_integrable
        H N hN beta hbeta B F)
      (posterior_local_covariance_bcf_integrable
        H N hN beta hbeta B G)

/-- Posterior mean is real-linear under scalar multiplication. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_smul_bcf
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (c : ℝ)
    (G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B (c • G) =
      c *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B G := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    (∫ A,
      c * G A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
        H N hN beta hbeta B) =
      c *
        ∫ A, G A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B
  exact integral_const_mul c (fun A => G A)

/-- Posterior covariance is additive in its right bounded-continuous slot. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_add_right_bcf
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F G K : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F (G + K) =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F G +
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F K := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  have hFG :
      Integrable (fun A => F A * G A) mu :=
    (F.continuous.mul G.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFK :
      Integrable (fun A => F A * K A) mu :=
    (F.continuous.mul K.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_add_bcf
      H N hN beta hbeta B G K]
  change
    (∫ A, F A * (G A + K A) ∂mu) -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B F *
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B G +
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B K) =
      ((∫ A, F A * G A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B F *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B G) +
        ((∫ A, F A * K A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B F *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B K)
  have hInt :
      (∫ A, F A * (G A + K A) ∂mu) =
        (∫ A, F A * G A ∂mu) +
          ∫ A, F A * K A ∂mu := by
    simpa [mul_add] using integral_add hFG hFK
  rw [hInt]
  ring

/-- Posterior covariance is real-linear in its right bounded-continuous slot. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_smul_right_bcf
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (c : ℝ)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F (c • G) =
      c *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F G := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_smul_bcf
      H N hN beta hbeta B c G]
  change
    (∫ A, F A * (c * G A) ∂mu) -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B F *
          (c *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B G) =
      c *
        ((∫ A, F A * G A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B F *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B G)
  have hInt :
      (∫ A, F A * (c * G A) ∂mu) =
        c * ∫ A, F A * G A ∂mu := by
    calc
      (∫ A, F A * (c * G A) ∂mu) =
          ∫ A, c * (F A * G A) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with A
        ring
      _ = c * ∫ A, F A * G A ∂mu := by
        rw [integral_const_mul]
  rw [hInt]
  ring

/-- Posterior covariance commutes with a finite sum in its right slot. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_finset_sum_right_bcf
    {alpha : Type*}
    [DecidableEq alpha]
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (G : alpha →
      BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (s : Finset alpha) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F (s.sum G) =
      s.sum
        (fun i =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B F (G i)) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_add_right_bcf]
      exact congrArg
        (fun x =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B F (G i) + x)
        ih

/-- Posterior covariance is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_comm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F G =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B G F := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  have hProduct :
      (∫ A,
          F A * G A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B) =
        ∫ A,
          G A * F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B := by
    apply integral_congr_ae
    filter_upwards [] with A
    ring
  rw [hProduct]
  ring

/-- Posterior one-link conditional expectation fixes observables already
constant on the target-link fibers. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_fixes_of_offTargetFiberConstant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiber :
      ∀
        A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
          A C target →
        O A = O C)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target =
      O A := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target
  have hPoint :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        O (Function.update A target g) = O A := by
    intro g
    apply hFiber (Function.update A target g) A
    intro e he
    simp [Function.update, he]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
  change (∫ g, O (Function.update A target g) ∂mu) = O A
  simp_rw [hPoint]
  simp

/-- A target-fiber-constant left factor pulls through the exact posterior
one-link conditional expectation of a product. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_mul_of_left_offTargetFiberConstant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiber :
      ∀
        A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
          A C target →
        F A = F C)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B (F * G) A target =
      F A *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B G A target := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  have hPoint :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        F (Function.update A target g) = F A := by
    intro g
    apply hFiber (Function.update A target g) A
    intro e he
    simp [Function.update, he]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
  change
    (∫ g,
      F (Function.update A target g) * G (Function.update A target g) ∂mu) =
      F A * ∫ g, G (Function.update A target g) ∂mu
  simp_rw [hPoint]
  rw [integral_const_mul]

/-- One-link posterior fluctuation is pointwise bounded by any declared
variation bound at that same coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkFluctuation_abs_le_variation
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => O A))
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |O A -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target| ≤
      P.variation target := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target
  have hOInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          O (Function.update A target g))
        mu := by
    exact
      (O.continuous.comp
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
          H N target).comp
          (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
  have hConstInt :
      Integrable
        (fun _g : Matrix.specialUnitaryGroup (Fin N) ℂ => O A)
        mu :=
    integrable_const _
  have hDiffInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          O A - O (Function.update A target g))
        mu :=
    hConstInt.sub' hOInt
  have hAbsDiffInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          |O A - O (Function.update A target g)|)
        mu := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hVarInt :
      Integrable
        (fun _g : Matrix.specialUnitaryGroup (Fin N) ℂ => P.variation target)
        mu :=
    integrable_const _
  have hVariation :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |O A - O (Function.update A target g)| ≤ P.variation target := by
    intro g
    apply P.variation_bound target A (Function.update A target g)
    intro e he
    simp [Function.update, he]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
  change
    |O A -
      ∫ g, O (Function.update A target g) ∂mu| ≤
      P.variation target
  calc
    |O A - ∫ g, O (Function.update A target g) ∂mu| =
        |(∫ _g, O A ∂mu) -
          ∫ g, O (Function.update A target g) ∂mu| := by
      simp
    _ =
      |∫ g, O A - O (Function.update A target g) ∂mu| := by
      rw [integral_sub hConstInt hOInt]
    _ ≤
      ∫ g, |O A - O (Function.update A target g)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
      ∫ _g, P.variation target ∂mu := by
      apply integral_mono hAbsDiffInt hVarInt
      intro g
      exact hVariation g
    _ = P.variation target := by simp

/-- The posterior mean of a one-link fluctuation vanishes exactly by global
one-link stationarity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuation_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (O -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target O) =
      0 := by
  let PO :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target O
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  have hOInt :=
    posterior_local_covariance_bcf_integrable
      H N hN beta hbeta B O
  have hPOInt :=
    posterior_local_covariance_bcf_integrable
      H N hN beta hbeta B PO
  change
    (∫ A, O A - PO A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
        H N hN beta hbeta B) = 0
  rw [integral_sub hOInt hPOInt]
  have hStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target O
  simpa [PO] using sub_eq_zero.mpr hStationary.symm

/-- A source-local factor has exact zero covariance defect under every
different-coordinate posterior update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_sub_conditionalExpectation_eq_zero_of_ne
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (hNe : target ≠ source) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O) =
      0 := by
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let PO :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target O
  have hFiber :
      ∀
        A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
          A C target →
        L A = L C := by
    intro A C hAgree
    have hSource : A source = C source :=
      hAgree source (Ne.symm hNe)
    unfold L
    simp only [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_apply]
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    rw [hSource]
  have hProductStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target (L * O)
  have hMeanStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target O
  have hPair :
      (∫ A, L A * O A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B) =
      ∫ A, L A * PO A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B := by
    calc
      (∫ A, L A * O A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B) =
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta B (L * O) A target
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B :=
        hProductStationary.symm
      _ =
        ∫ A, L A * PO A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B := by
        apply integral_congr_ae
        filter_upwards [] with A
        simpa [PO] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_mul_of_left_offTargetFiberConstant
            H N hN beta hbeta B L O target hFiber A
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  rw [hPair]
  have hMeanEq :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B PO =
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B O := by
    simpa [PO,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean] using
      hMeanStationary
  rw [hMeanEq]
  ring

/-- The source local factor is uniformly centered in the Harnack interval with
radius exactly half the Harnack width. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_abs_sub_harnackMidpoint_le_half_width
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source sourceValue -
        (Real.exp (-8 * beta) + Real.exp (8 * beta)) / 2| ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta / 2 := by
  have hLower :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta A B source sourceValue
  have hUpper :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B source sourceValue
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
  rw [abs_le]
  constructor <;> linarith

/-- At the source coordinate, the local-factor covariance defect is controlled
by half its Harnack width times the source variation of the right observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_sub_conditionalExpectation_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => O A)) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B source O)| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta / 2) *
        P.variation source := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let PO :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B source O
  let Q : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
    O - PO
  let center : ℝ :=
    (Real.exp (-8 * beta) + Real.exp (8 * beta)) / 2
  let radius : ℝ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta / 2
  have hQMean :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B Q = 0 := by
    simpa [Q, PO] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuation_eq_zero
        H N hN beta hbeta B O source
  have hQPoint :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |Q A| ≤ P.variation source := by
    intro A
    simpa [Q, PO] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkFluctuation_abs_le_variation
        O P source A
  have hLPoint :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |L A - center| ≤ radius := by
    intro A
    simpa [L, center, radius] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_abs_sub_harnackMidpoint_le_half_width
        H N hN beta hbeta A B source sourceValue
  have hQInt :
      Integrable (fun A => Q A) mu :=
    Q.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLQInt :
      Integrable (fun A => (L A - center) * Q A) mu :=
    ((L.continuous.sub continuous_const).mul Q.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsInt :
      Integrable (fun A => |(L A - center) * Q A|) mu := by
    simpa [Real.norm_eq_abs] using hLQInt.norm
  have hConstInt :
      Integrable (fun _A :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          radius * P.variation source) mu :=
    integrable_const _
  have hRadius :
      0 ≤ radius := by
    exact div_nonneg
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta)
      (by norm_num)
  have hPointwise :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |(L A - center) * Q A| ≤ radius * P.variation source := by
    intro A
    rw [abs_mul]
    exact mul_le_mul
      (hLPoint A)
      (hQPoint A)
      (abs_nonneg _)
      hRadius
  have hCovDiff :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L O -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L PO =
      ∫ A, (L A - center) * Q A ∂mu := by
    have hOInt :=
      posterior_local_covariance_bcf_integrable
        H N hN beta hbeta B O
    have hPOInt :=
      posterior_local_covariance_bcf_integrable
        H N hN beta hbeta B PO
    have hLOInt :
        Integrable (fun A => L A * O A) mu :=
      (L.continuous.mul O.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hLPOInt :
        Integrable (fun A => L A * PO A) mu :=
      (L.continuous.mul PO.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    unfold
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    change
      ((∫ A, L A * O A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B L *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B O) -
        ((∫ A, L A * PO A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B L *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B PO) =
        ∫ A, (L A - center) * Q A ∂mu
    have hMeanEq :
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B O =
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B PO := by
      have hStationary :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
          H N hN beta hbeta B source O
      simpa [PO,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean] using
        hStationary.symm
    rw [hMeanEq]
    have hPairDiff :
        (∫ A, L A * O A ∂mu) -
          (∫ A, L A * PO A ∂mu) =
        ∫ A, L A * Q A ∂mu := by
      rw [← integral_sub hLOInt hLPOInt]
      apply integral_congr_ae
      filter_upwards [] with A
      simp [Q]
      ring
    have hQIntegral : (∫ A, Q A ∂mu) = 0 := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean] using
        hQMean
    calc
      ((∫ A, L A * O A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B L *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B PO) -
        ((∫ A, L A * PO A ∂mu) -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B L *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
              H N hN beta hbeta B PO) =
          (∫ A, L A * O A ∂mu) - (∫ A, L A * PO A ∂mu) := by
        ring
      _ = ∫ A, L A * Q A ∂mu := hPairDiff
      _ =
          ∫ A, ((L A - center) * Q A + center * Q A) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with A
        ring
      _ =
          (∫ A, (L A - center) * Q A ∂mu) +
            ∫ A, center * Q A ∂mu := by
        rw [integral_add hLQInt (hQInt.const_mul center)]
      _ =
          (∫ A, (L A - center) * Q A ∂mu) +
            center * ∫ A, Q A ∂mu := by
        rw [integral_const_mul]
      _ =
          ∫ A, (L A - center) * Q A ∂mu := by
        rw [hQIntegral]
        ring
  rw [hCovDiff]
  calc
    |∫ A, (L A - center) * Q A ∂mu| ≤
        ∫ A, |(L A - center) * Q A| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
        ∫ _A, radius * P.variation source ∂mu := by
      apply integral_mono hAbsInt hConstInt
      intro A
      exact hPointwise A
    _ = radius * P.variation source := by
      letI : IsProbabilityMeasure mu :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
          H N hN beta hbeta B
      simp [radius]

/-- One posterior uniform random-scan step changes covariance with a source
local factor by at most the source variation divided by the link count, times
half the local-factor Harnack width. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_sub_randomScan_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => O A))
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
          H N hN beta hbeta B O)| ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) * P.variation source) := by
  classical
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let PO :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
        H N hN beta hbeta B target O
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hnInvNonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hnPos.le
  have hRandomCov :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
            H N hN beta hbeta B O) =
        n⁻¹ *
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (PO target) := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
    rw [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_smul_right_bcf,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_finset_sum_right_bcf]
  have hExpand :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L O -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
            H N hN beta hbeta B O) =
      n⁻¹ *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L O -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (PO target)) := by
    rw [hRandomCov, Finset.sum_sub_distrib]
    have hConst :
        (∑ _target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B L O) =
        n *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B L O := by
      simp [n, nsmul_eq_mul]
    rw [hConst]
    field_simp [ne_of_gt hnPos]
  have hTerm :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B L O -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B L (PO target)| ≤
        if target = source then
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
            beta / 2) * P.variation source
        else 0 := by
    intro target
    by_cases h : target = source
    · subst target
      simp only [if_pos rfl]
      simpa [L, PO] using
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_sub_conditionalExpectation_abs_le
          H N hN beta hbeta B source sourceValue O P
    · have hZero :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_sub_conditionalExpectation_eq_zero_of_ne
          H N hN beta hbeta B source target sourceValue O h
      simp [h, L, PO, hZero]
  rw [hExpand, abs_mul, abs_of_nonneg hnInvNonneg]
  calc
    n⁻¹ *
        |∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L O -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (PO target))| ≤
      n⁻¹ *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L O -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (PO target)| := by
      apply mul_le_mul_of_nonneg_left _ hnInvNonneg
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
      n⁻¹ *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (if target = source then
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
              beta / 2) * P.variation source
          else 0) := by
      apply mul_le_mul_of_nonneg_left _ hnInvNonneg
      apply Finset.sum_le_sum
      intro target _
      exact hTerm target
    _ =
      n⁻¹ *
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) * P.variation source) := by
      congr 1
      simp

/-- Finite covariance telescope for a source-local posterior factor along the
actual posterior random-scan orbit. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScanCenteredState_partial_telescope_abs_le_finiteResolventProfile
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        (((P.toRandomScanCenteredState).randomScanIterate D M).observable)| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D P.variation M source := by
  classical
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let S : ℕ →
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N :=
    fun m => (P.toRandomScanCenteredState).randomScanIterate D m
  let radius : ℝ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta / 2
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hTel :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L O -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L (S M).observable =
      (Finset.range M).sum
        (fun m =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (S m).observable -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (S (m + 1)).observable) := by
    induction M with
    | zero =>
        simp [S,
          PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState.randomScanIterate,
          PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile.toRandomScanCenteredState]
    | succ M ih =>
        rw [Finset.sum_range_succ]
        rw [← ih]
        ring
  rw [hTel]
  calc
    |(Finset.range M).sum
        (fun m =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (S m).observable -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (S (m + 1)).observable)| ≤
      (Finset.range M).sum
        (fun m =>
          |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (S m).observable -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
              H N hN beta hbeta B L (S (m + 1)).observable|) := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
      (Finset.range M).sum
        (fun m =>
          n⁻¹ * (radius *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D P.variation m source)) := by
      apply Finset.sum_le_sum
      intro m _
      let Pm :
          PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
            H N (fun A => (S m).observable A) :=
        { variation := (S m).profile.variation
          variation_nonneg := (S m).profile.variation_nonneg
          variation_bound := (S m).profile.variation_bound }
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_sub_randomScan_abs_le
          H N hN beta hbeta B source sourceValue (S m).observable Pm hEdge
      have hObs :
          (S (m + 1)).observable =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
              H N hN beta hbeta B (S m).observable := by
        simpa [S] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_succ_observable
            (P.toRandomScanCenteredState) D m
      rw [hObs]
      have hVar :
          Pm.variation =
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D P.variation m := by
        change
          (S m).profile.variation =
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D P.variation m
        simpa [S] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_variation_eq
            P D m
      simpa [L, n, radius, Pm, hVar] using hStep
    _ =
      radius *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D P.variation M source := by
      unfold
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum]
      have hRadiusSum :
          (Finset.range M).sum
              (fun m =>
                radius *
                  periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
                    D P.variation m source) =
            radius *
              (Finset.range M).sum
                (fun m =>
                  periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
                    D P.variation m source) := by
        rw [Finset.mul_sum]
      rw [hRadiusSum]
      ring

end

end MathlibAnalytic
end MGAP4D
