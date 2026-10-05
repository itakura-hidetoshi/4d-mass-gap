import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanDoeblinObservableContraction
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Geometric posterior block oscillation contraction

Iterating complete posterior random-scan blocks contracts every declared global
pairwise oscillation bound by rho^k, with rho = 1 - delta < 1.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local instance posteriorRandomScanDoeblinGeometricSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorRandomScanDoeblinGeometricTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRandomScanDoeblinGeometricCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRandomScanDoeblinGeometricSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRandomScanDoeblinGeometricMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRandomScanDoeblinGeometricBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Iteration of complete posterior random-scan blocks on real observables. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    ℕ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ
  | 0 => f
  | n + 1 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectation
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B f n)

/-- Strong measurability is preserved by every posterior full-block iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f) :
    ∀ n,
      StronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B f n) := by
  intro n
  induction n with
  | zero =>
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
      ] using hf
  | succ n ih =>
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectation
      exact ih.integral_kernel

/-- After k complete posterior random-scan blocks, a global pairwise
oscillation bound contracts by rho^k. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_difference_abs_le_pow_residualMass_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X - f Y| ≤ R) :
    ∀ k A C,
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B f k A -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B f k C| ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
          H beta).toReal ^ k * R := by
  intro k
  induction k with
  | zero =>
      intro A C
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
      ] using hOsc A C
  | succ k ih =>
      intro A C
      let fk :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B f k
      let rho : ℝ :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
          H beta).toReal
      have hfkStrong : StronglyMeasurable fk := by
        dsimp [fk]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B f hf k
      have hBoundNonneg : 0 ≤ rho ^ k * R := by
        positivity
      have hOne :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectation_difference_abs_le_residualMass_mul
          H N hN beta hbeta B fk hfkStrong
          (rho ^ k * R) hBoundNonneg (fun X Y => by
            simpa [fk, rho] using ih X Y) A C
      calc
        |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
            H N hN beta hbeta B f (k + 1) A -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
            H N hN beta hbeta B f (k + 1) C| ≤
            rho * (rho ^ k * R) := by
              simpa [
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate,
                fk,
                rho
              ] using hOne
        _ = rho ^ (k + 1) * R := by
          rw [pow_succ]
          ring

/-- The real posterior residual factor is strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_toReal_lt_one
    (H : ℕ)
    (beta : ℝ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta).toReal < 1 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_lt_one
      H beta
  simpa using
    (ENNReal.toReal_lt_toReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_ne_top
        H beta)
      ENNReal.one_ne_top).2 h

/-- The geometric posterior residual factor tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
    (H : ℕ)
    (beta : ℝ) :
    Tendsto
      (fun k : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
          H beta).toReal ^ k)
      atTop
      (𝓝 0) := by
  exact
    tendsto_pow_atTop_nhds_zero_of_lt_one
      ENNReal.toReal_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_toReal_lt_one
        H beta)

end

end MathlibAnalytic
end MGAP4D
