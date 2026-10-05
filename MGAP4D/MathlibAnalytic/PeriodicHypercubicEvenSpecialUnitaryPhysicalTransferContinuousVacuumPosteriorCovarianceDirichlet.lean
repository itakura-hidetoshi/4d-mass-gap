import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorResponseCovarianceBridge
import Mathlib.Tactic

/-!
# Posterior one-link covariance projection and Dirichlet control

The continuous-vacuum posterior one-link conditional expectation is now known
to be:

* Feller on bounded-continuous observables;
* exactly stationary for the posterior law;
* equipped with sharp linkwise non-strict variation propagation.

This file closes the missing projection algebra at the posterior covariance
level.  For the exact target-link conditional expectation P_t we prove:

* P_t is pointwise idempotent on the BCF carrier;
* projected factors can be pulled through a second target-link conditional
  expectation;
* P_t is self-adjoint for the posterior pairing and covariance;
* the fluctuation Q_t = I - P_t has zero posterior mean;
* |Q_t F| is controlled by any valid target-link variation bound;
* the one-link posterior Dirichlet defect satisfies
    |Cov(F,G) - Cov(F,P_t G)| <= v_F(t) v_G(t).

These are the exact local identities needed to transfer the finite Wilson
random-scan covariance telescope to the posterior carrier in the next step.

No strict Dobrushin row-sum bound, covariance decay, infinite resolvent,
posterior fixed point, heat-bath-time / Euclidean-time identification,
H1-D5 exact descent, or complete Yang--Mills mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorCovarianceDirichletTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorCovarianceDirichletCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorCovarianceDirichletSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorCovarianceDirichletMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorCovarianceDirichletBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- One posterior target-link conditional expectation is unchanged after
pre-replacing that same target coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationBCF_update_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O (Function.update A target g) target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_of_agreeOffTarget
      H N hN beta hbeta B (Function.update A target g) A target O
  intro e he
  simp [Function.update, he]

/-- The bounded-continuous posterior target-link projection is pointwise
idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationContinuousBCF_idempotent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
        H N hN beta hbeta B target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
        H N hN beta hbeta B target O := by
  ext A
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationBCF_update_target]
  simp

/-- A projected left factor pulls through a second conditional expectation at
the same posterior target link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationBCF_projected_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target F) * O)
        A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B F A target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
  change
    (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target F (Function.update A target g) *
        O (Function.update A target g) ∂mu) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B F A target *
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          O (Function.update A target g) ∂mu
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationBCF_update_target]
  rw [integral_const_mul]

/-- Posterior mean is preserved by one exact target-link conditional
expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkConditionalExpectationContinuousBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O) =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B O := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target O

/-- Self-adjointness of one exact posterior conditional expectation for the
posterior product pairing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_integral_singleLinkConditionalExpectationContinuousBCF_mul_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target F A * O A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B) =
      ∫ A,
        F A *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target O A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B := by
  let PF :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target F
  let PO :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target O
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  have hLeftStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target (PF * O)
  have hRightStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target (PO * F)
  have hLeftPoint :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta B (PF * O) A target =
          PF A * PO A := by
    intro A
    simpa [PF, PO] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationBCF_projected_mul
        H N hN beta hbeta B target F O A
  have hRightPoint :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta B (PO * F) A target =
          PO A * PF A := by
    intro A
    simpa [PF, PO] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationBCF_projected_mul
        H N hN beta hbeta B target O F A
  change (∫ A, PF A * O A ∂mu) = ∫ A, F A * PO A ∂mu
  calc
    (∫ A, PF A * O A ∂mu) =
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta B (PF * O) A target ∂mu := by
      rw [hLeftStationary]
    _ = ∫ A, PF A * PO A ∂mu := by
      apply integral_congr_ae
      filter_upwards with A
      exact hLeftPoint A
    _ = ∫ A, PO A * PF A ∂mu := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = ∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta B (PO * F) A target ∂mu := by
      apply integral_congr_ae
      filter_upwards with A
      exact (hRightPoint A).symm
    _ = ∫ A, PO A * F A ∂mu := hRightStationary
    _ = ∫ A, F A * PO A ∂mu := by
      apply integral_congr_ae
      filter_upwards with A
      ring

/-- One posterior target-link conditional expectation is self-adjoint for the
posterior covariance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_singleLinkConditionalExpectationContinuousBCF_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target F)
        O =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_integral_singleLinkConditionalExpectationContinuousBCF_mul_symm
      H N hN beta hbeta B target F O,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target F,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target O]

/-- Posterior one-link fluctuation Q_t = I - P_t on the bounded-continuous
carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  F -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target F

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
        H N hN beta hbeta B target F A =
      F A -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B F A target := by
  rfl

/-- A posterior one-link fluctuation is pointwise controlled by any valid
variation bound at that target link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF_abs_le_variation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => F A))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
        H N hN beta hbeta B target F A| ≤
      P.variation target := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta B A target
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta B A target
  have hFInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (Function.update A target g))
        mu :=
    (F.continuous.comp
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
        H N target).comp
        (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hConstInt :
      Integrable
        (fun _g : Matrix.specialUnitaryGroup (Fin N) ℂ => F A)
        mu :=
    integrable_const _
  have hDiffInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F A - F (Function.update A target g))
        mu :=
    hConstInt.sub' hFInt
  have hAbsDiffInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          |F A - F (Function.update A target g)|)
        mu := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hVariationInt :
      Integrable
        (fun _g : Matrix.specialUnitaryGroup (Fin N) ℂ => P.variation target)
        mu :=
    integrable_const _
  have hVariation :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |F A - F (Function.update A target g)| ≤ P.variation target := by
    intro g
    apply P.variation_bound target A (Function.update A target g)
    intro source hsource
    simp [Function.update, hsource]
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
  change
    |F A -
      ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        F (Function.update A target g) ∂mu| ≤
      P.variation target
  calc
    |F A -
      ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        F (Function.update A target g) ∂mu| =
      |(∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ, F A ∂mu) -
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          F (Function.update A target g) ∂mu| := by
      simp
    _ =
      |∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        F A - F (Function.update A target g) ∂mu| := by
      rw [integral_sub hConstInt hFInt]
    _ ≤
      ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |F A - F (Function.update A target g)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
      ∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        P.variation target ∂mu := by
      apply integral_mono hAbsDiffInt hVariationInt
      intro g
      exact hVariation g
    _ = P.variation target := by simp

/-- The posterior mean of every one-link fluctuation is exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuationContinuousBCF_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
          H N hN beta hbeta B target F) = 0 := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let PF :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target F
  have hFInt : Integrable (fun A => F A) mu :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPFInt : Integrable (fun A => PF A) mu :=
    PF.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
  change (∫ A, F A - PF A ∂mu) = 0
  rw [integral_sub hFInt hPFInt]
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target F
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean at hMean
  change (∫ A, PF A ∂mu) = ∫ A, F A ∂mu at hMean
  rw [hMean]
  ring

/-- Two posterior one-link fluctuations satisfy the local two-sided covariance
bound at that same target link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_singleLinkFluctuations_abs_le_variation_mul_variation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (PF :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => F A))
    (PG :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => G A)) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
          H N hN beta hbeta B target F)
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
          H N hN beta hbeta B target G)| ≤
      PF.variation target * PG.variation target := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let QF :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
      H N hN beta hbeta B target F
  let QG :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
      H N hN beta hbeta B target G
  have hQFZero :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B QF = 0 := by
    simpa [QF] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuationContinuousBCF_eq_zero
        H N hN beta hbeta B target F
  have hQGZero :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B QG = 0 := by
    simpa [QG] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuationContinuousBCF_eq_zero
        H N hN beta hbeta B target G
  have hProductInt :
      Integrable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          QF A * QG A)
        mu :=
    (QF.continuous.mul QG.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsProductInt :
      Integrable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          |QF A * QG A|)
        mu := by
    simpa [Real.norm_eq_abs] using hProductInt.norm
  have hConstInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          PF.variation target * PG.variation target)
        mu :=
    integrable_const _
  have hPointwise :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |QF A * QG A| ≤ PF.variation target * PG.variation target := by
    intro A
    rw [abs_mul]
    exact mul_le_mul
      (by
        simpa [QF] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF_abs_le_variation
            H N hN beta hbeta B target F PF A)
      (by
        simpa [QG] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF_abs_le_variation
            H N hN beta hbeta B target G PG A)
      (abs_nonneg _)
      (PF.variation_nonneg target)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  change
    |(∫ A, QF A * QG A ∂mu) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B QF *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B QG| ≤
      PF.variation target * PG.variation target
  rw [hQFZero, hQGZero]
  simp only [zero_mul, sub_zero]
  calc
    |∫ A, QF A * QG A ∂mu| ≤
        ∫ A, |QF A * QG A| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
        ∫ _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          PF.variation target * PG.variation target ∂mu := by
      apply integral_mono hAbsProductInt hConstInt
      intro A
      exact hPointwise A
    _ = PF.variation target * PG.variation target := by
      letI : IsProbabilityMeasure mu :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
          H N hN beta hbeta B
      simp

/-- Posterior one-link covariance defect equals the covariance of the two
corresponding one-link fluctuations. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_sub_singleLinkConditionalExpectation_eq_fluctuation_pairing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F G -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target G) =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
          H N hN beta hbeta B target F)
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
          H N hN beta hbeta B target G) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let PF :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target F
  let PG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target G
  let QF :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
      H N hN beta hbeta B target F
  let QG :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSingleLinkFluctuationContinuousBCF
      H N hN beta hbeta B target G
  have hPair :
      (∫ A, PF A * G A ∂mu) = ∫ A, F A * PG A ∂mu := by
    simpa [PF, PG, mu] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_integral_singleLinkConditionalExpectationContinuousBCF_mul_symm
        H N hN beta hbeta B target F G
  have hPairProjected :
      (∫ A, PF A * PG A ∂mu) = ∫ A, F A * PG A ∂mu := by
    have hSymm :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_integral_singleLinkConditionalExpectationContinuousBCF_mul_symm
        H N hN beta hbeta B target F PG
    have hId :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_singleLinkConditionalExpectationContinuousBCF_idempotent
        H N hN beta hbeta B target G
    rw [hId] at hSymm
    simpa [PF, PG, mu] using hSymm
  have hQFZero :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B QF = 0 := by
    simpa [QF] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuationContinuousBCF_eq_zero
        H N hN beta hbeta B target F
  have hQGZero :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B QG = 0 := by
    simpa [QG] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkFluctuationContinuousBCF_eq_zero
        H N hN beta hbeta B target G
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  change
    ((∫ A, F A * G A ∂mu) -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B F *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B G) -
      ((∫ A, F A * PG A ∂mu) -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B F *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B PG) =
      (∫ A, QF A * QG A ∂mu) -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B QF *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
            H N hN beta hbeta B QG
  have hMeanG :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_singleLinkConditionalExpectationContinuousBCF
      H N hN beta hbeta B target G
  change
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B PG =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B G at hMeanG
  rw [hMeanG, hQFZero, hQGZero]
  simp only [zero_mul, sub_zero]
  have hFInt : Integrable (fun A => F A) mu :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGInt : Integrable (fun A => G A) mu :=
    G.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPFInt : Integrable (fun A => PF A) mu :=
    PF.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPGInt : Integrable (fun A => PG A) mu :=
    PG.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hExpand :
      (∫ A, QF A * QG A ∂mu) =
        (∫ A, F A * G A ∂mu) -
          (∫ A, F A * PG A ∂mu) -
          (∫ A, PF A * G A ∂mu) +
          (∫ A, PF A * PG A ∂mu) := by
    change
      (∫ A, (F A - PF A) * (G A - PG A) ∂mu) =
        (∫ A, F A * G A ∂mu) -
          (∫ A, F A * PG A ∂mu) -
          (∫ A, PF A * G A ∂mu) +
          (∫ A, PF A * PG A ∂mu)
    have hFG : Integrable (fun A => F A * G A) mu := hFInt.mul hGInt
    have hFPG : Integrable (fun A => F A * PG A) mu := hFInt.mul hPGInt
    have hPFG : Integrable (fun A => PF A * G A) mu := hPFInt.mul hGInt
    have hPFPG : Integrable (fun A => PF A * PG A) mu := hPFInt.mul hPGInt
    calc
      (∫ A, (F A - PF A) * (G A - PG A) ∂mu) =
          ∫ A,
            ((F A * G A - F A * PG A) -
              (PF A * G A - PF A * PG A)) ∂mu := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ =
          (∫ A, F A * G A - F A * PG A ∂mu) -
            (∫ A, PF A * G A - PF A * PG A ∂mu) := by
        rw [
          integral_sub
            (hFG.sub' hFPG)
            (hPFG.sub' hPFPG)]
      _ =
          ((∫ A, F A * G A ∂mu) - (∫ A, F A * PG A ∂mu)) -
            ((∫ A, PF A * G A ∂mu) - (∫ A, PF A * PG A ∂mu)) := by
        rw [integral_sub hFG hFPG, integral_sub hPFG hPFPG]
      _ =
          (∫ A, F A * G A ∂mu) -
            (∫ A, F A * PG A ∂mu) -
            (∫ A, PF A * G A ∂mu) +
            (∫ A, PF A * PG A ∂mu) := by
        ring
  rw [hExpand, hPair, hPairProjected]
  ring

/-- The posterior one-link Dirichlet covariance defect is bounded by the
product of the two target-link variation bounds. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_sub_singleLinkConditionalExpectation_abs_le_variation_mul_variation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (PF :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => F A))
    (PG :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N (fun A => G A)) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F G -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target G)| ≤
      PF.variation target * PG.variation target := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_sub_singleLinkConditionalExpectation_eq_fluctuation_pairing
      H N hN beta hbeta B target F G]
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_singleLinkFluctuations_abs_le_variation_mul_variation
      H N hN beta hbeta B target F G PF PG

end

end MathlibAnalytic
end MGAP4D
