import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorLocalFactor
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

/-!
# Continuous-vacuum posterior probability and exact target-update expectation

PR #5154 constructs the positive continuous raw posterior weight

  P_B(A) = Omega(A) * K(A,B)

and proves the two exact identities

  integral P_B = lambda * Omega(B),

  integral P_B(A) * L_{B,target,g}(A)
    = lambda * Omega(B[target := g]).

This file normalizes P_B with Mathlib's canonical exponentially tilted measure.
Since P_B is strictly positive and continuous, log P_B is a continuous
exponent whose exponential is exactly P_B.  The resulting posterior law is
therefore a genuine probability measure, and integral_tilted turns the second
identity above into

  E_{pi_B}[L_{B,target,g}]
    = Omega(B[target := g]) / Omega(B).

This is the normalization bridge needed before comparing two remote-source
posteriors.  No Dobrushin decay, Euclidean-time identification, H1-D5 exact
descent, or complete Yang--Mills mass-gap claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance continuousVacuumPosteriorProbabilityTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumPosteriorProbabilityCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumPosteriorProbabilitySecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumPosteriorProbabilityMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumPosteriorProbabilityBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Logarithm of the positive continuous raw posterior weight. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  Real.log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
      H N hN beta hbeta B A)

/-- The posterior log weight is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
        H N hN beta hbeta B) := by
  have hWeight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_continuous
      H N hN beta hbeta B
  have hNonzero :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
          H N hN beta hbeta B A ≠ 0 := fun A =>
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_pos
        H N hN beta hbeta B A)
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
  ] using hWeight.log hNonzero

/-- Exponentiating the posterior log weight recovers the raw posterior weight
exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Real.exp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
          H N hN beta hbeta B A) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
        H N hN beta hbeta B A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
  exact Real.exp_log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_pos
      H N hN beta hbeta B A)

/-- The exponential posterior log weight is Haar-integrable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        Real.exp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
            H N hN beta hbeta B A))
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  have hWeightInt :
      Integrable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
          H N hN beta hbeta B)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_continuous
      H N hN beta hbeta B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp
  ] using hWeightInt

/-- Canonical normalized posterior law on the left boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).tilted
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
      H N hN beta hbeta B)

/-- The normalized posterior law is a genuine probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
        H N hN beta hbeta B) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
  exact
    MeasureTheory.isProbabilityMeasure_tilted
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp_integrable
        H N hN beta hbeta B)

/-- The tilted partition function is exactly lambda times the continuous vacuum
at the fixed right boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp_integral_eq_topNorm_mul_vacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        Real.exp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
            H N hN beta hbeta B A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B := by
  calc
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        Real.exp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
            H N hN beta hbeta B A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
          H N hN beta hbeta B A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with A
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp
          H N hN beta hbeta B A
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_integral_eq_topNorm_mul_vacuum
        H N hN beta hbeta B

/-- Exact posterior expectation formula for the local target-update factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_expectation_localFactor_eq_vacuum_ratio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g
        ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target g) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  have hlambda : 0 < lambda := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  have hOmega :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
  rw [MeasureTheory.integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp_integral_eq_topNorm_mul_vacuum
      H N hN beta hbeta B]
  have hNumerator :
      (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          Real.exp
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
                H N hN beta hbeta B A) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g
          ∂μ) =
        lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update B target g) := by
    calc
      (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          Real.exp
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
                H N hN beta hbeta B A) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g
          ∂μ) =
        ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
              H N hN beta hbeta B A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g
          ∂μ := by
            apply integral_congr_ae
            filter_upwards with A
            rw [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp
                H N hN beta hbeta B A]
      _ =
        lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update B target g) := by
          symm
          simpa [lambda, μ] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_update_eq_integral_posterior_mul_localFactor
              H N hN beta hbeta B target g
  rw [hNumerator]
  change
    (lambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target g)) /
      (lambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B) =
    _
  field_simp [hlambda.ne', hOmega.ne']

end

end MathlibAnalytic
end MGAP4D
