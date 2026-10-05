import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSourceRetilt
import Mathlib.Tactic

/-!
# Vacuum cross-ratio as posterior local-tilt response

PR #5155 writes a continuous-vacuum target-update ratio as an expectation of
the exact target-local Wilson factor under the posterior probability pi_B.
PR #5156 identifies a right-source update with a source-local exponential
re-tilt of that posterior and, for a remote target/source pair, keeps the
target-local observable itself unchanged.

This file combines those two exact identities.  The continuous-vacuum
four-point mixed log difference is exactly the difference of two logarithmic
posterior expectation responses, one for each inserted target value.

Consequently, if every target value has logarithmic posterior response bounded
in absolute value by r, then the vacuum cross-ratio radius is at most 2*r.
Together with PR #5153 this immediately gives the complete continuous
ground-state target-fiber TV receiver.

The remaining analytic task is therefore quantitative control of one
target-local expectation under one remote source-local re-tilt.  No such decay
estimate, Euclidean-time identification, H1-D5 exact descent, or complete
Yang--Mills mass-gap claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance vacuumCrossRatioPosteriorResponseTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumCrossRatioPosteriorResponseCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumCrossRatioPosteriorResponseSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumCrossRatioPosteriorResponseMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumCrossRatioPosteriorResponseBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Target-local factor expectation under the base continuous-vacuum
posterior. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
    ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B)

/-- The same target-local factor expectation after the base posterior is
re-tilted by one right-source local factor. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
    ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
        H N hN beta hbeta B).tilted
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
        H N beta B source sourceValue))

/-- The base posterior expectation is exactly the continuous-vacuum target
update ratio. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
        H N hN beta hbeta B target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target g) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_expectation_localFactor_eq_vacuum_ratio
      H N hN beta hbeta B target g

/-- For a plaquette-remote source, the source-re-tilted target expectation is
exactly the target-update vacuum ratio in the source-updated environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
        H N hN beta hbeta B target source sourceValue g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source sourceValue) target g) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B source sourceValue) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_remoteSource_targetRatio_eq_tiltedPosteriorExpectation
      H N hN beta hbeta B target source sourceValue g hNe hRemote).symm

/-- The base target expectation is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
        H N hN beta hbeta B target g := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio]
  exact div_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta (Function.update B target g))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B)

/-- Under remote target/source separation, the source-re-tilted target
expectation is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
        H N hN beta hbeta B target source sourceValue g := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
      H N hN beta hbeta B target source sourceValue g hNe hRemote]
  exact div_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (Function.update (Function.update B source sourceValue) target g))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta (Function.update B source sourceValue))

/-- Exact identification of the continuous-vacuum mixed four-point log
difference with the difference of logarithmic posterior expectation responses. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_crossDifference_eq_posteriorLogResponse
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta B target u -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta (Function.update B source sourceValue) target u) -
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta B target v -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta (Function.update B source sourceValue) target v) =
    (Real.log
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
            H N hN beta hbeta B target u) -
        Real.log
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
            H N hN beta hbeta B target source sourceValue u)) -
      (Real.log
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
            H N hN beta hbeta B target v) -
        Real.log
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
            H N hN beta hbeta B target source sourceValue v)) := by
  have hBaseU :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio
      H N hN beta hbeta B target u
  have hBaseV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio
      H N hN beta hbeta B target v
  have hTiltU :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
      H N hN beta hbeta B target source sourceValue u hNe hRemote
  have hTiltV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
      H N hN beta hbeta B target source sourceValue v hNe hRemote
  have hB :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta B)
  have hBs :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B source sourceValue) ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (Function.update B source sourceValue))
  have hBu :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target u) ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (Function.update B target u))
  have hBv :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target v) ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (Function.update B target v))
  have hBsu :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source sourceValue) target u) ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta
        (Function.update (Function.update B source sourceValue) target u))
  have hBsv :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source sourceValue) target v) ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta
        (Function.update (Function.update B source sourceValue) target v))
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
  rw [hBaseU, hBaseV, hTiltU, hTiltV]
  rw [
    Real.log_div hBu hB,
    Real.log_div hBv hB,
    Real.log_div hBsu hBs,
    Real.log_div hBsv hBs]
  ring

/-- Uniform absolute logarithmic response bound for the target-local posterior
expectation under one source-local re-tilt. -/
def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLogResponseBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (r : ℝ) : Prop :=
  ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    |Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
          H N hN beta hbeta B target g) -
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
          H N hN beta hbeta B target source sourceValue g)| ≤ r

/-- A uniform logarithmic posterior response bound r yields vacuum cross-ratio
radius 2*r for every remote target/source pair. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight_crossRatioBound_of_posteriorLogResponse
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (r : ℝ)
    (hResponse :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLogResponseBound
        H N hN beta hbeta B target source sourceValue r) :
    ContinuousNormalizedExpCrossRatioBound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
        H N hN beta hbeta B target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
        H N hN beta hbeta (Function.update B source sourceValue) target)
      (2 * r) := by
  intro u v
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_crossDifference_eq_posteriorLogResponse
      H N hN beta hbeta B target source sourceValue u v hNe hRemote]
  have hu := hResponse u
  have hv := hResponse v
  have huUpper := (abs_le.mp hu).2
  have hvLower := (abs_le.mp hv).1
  linarith

/-- Combining the posterior-response receiver with PR #5153 gives the sharp
complete target-fiber half-L1/TV estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_remoteSource_posteriorLogResponse
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (r : ℝ)
    (hr : 0 ≤ r)
    (hResponse :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLogResponseBound
        H N hN beta hbeta B target source sourceValue r) :
    (2 : ℝ)⁻¹ *
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left B target g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left
                (Function.update B source sourceValue) target g|
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      (Real.exp (2 * r) - 1) / (Real.exp (2 * r) + 1) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_remoteSource_vacuumCrossRatio
      H N hN beta hbeta left B target source sourceValue
      hNe hRemote (2 * r) (mul_nonneg (by norm_num) hr)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight_crossRatioBound_of_posteriorLogResponse
      H N hN beta hbeta B target source sourceValue
      hNe hRemote r hResponse

end

end MathlibAnalytic
end MGAP4D
