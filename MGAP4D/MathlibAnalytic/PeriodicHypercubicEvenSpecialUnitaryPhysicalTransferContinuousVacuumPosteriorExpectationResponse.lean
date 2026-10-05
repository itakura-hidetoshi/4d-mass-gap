import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumCrossRatioPosteriorResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack
import Mathlib.Tactic

/-!
# Posterior expectation discrepancy to logarithmic response

PR #5157 reduces the remote-source continuous-vacuum cross-ratio to a uniform
logarithmic response of one target-local posterior expectation.

This file removes the logarithm from the remaining analytic input.

First, a generic real inequality is proved:

  if m > 0, m <= x, m <= y,
  then |log x - log y| <= |x - y| / m.

Next, the volume-uniform one-link vacuum Harnack theorem gives the exact lower
floor

  exp (-8 * beta)

for both the base posterior target expectation and, under remote source
separation, the source-re-tilted target expectation.

Therefore a uniform ordinary expectation discrepancy epsilon implies a
log-response radius

  epsilon / exp (-8 * beta),

hence a vacuum cross-ratio radius twice that quantity and the corresponding
sharp complete target-fiber half-L1/TV estimate.

The remaining model-specific task is now an ordinary expectation-response
bound under one remote source-local tilt.  No such decay estimate,
Euclidean-time identification, H1-D5 exact descent, or complete Yang--Mills
mass-gap claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorExpectationToLogResponseTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorExpectationToLogResponseCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorExpectationToLogResponseSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorExpectationToLogResponseMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorExpectationToLogResponseBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Logarithm is 1/m-Lipschitz on the positive half-line above m. -/
private theorem abs_log_sub_log_le_abs_sub_div_lower
    {x y m : ℝ}
    (hm : 0 < m)
    (hmx : m ≤ x)
    (hmy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m := by
  have hx : 0 < x := lt_of_lt_of_le hm hmx
  have hy : 0 < y := lt_of_lt_of_le hm hmy
  have hUpper :
      Real.log x - Real.log y ≤ |x - y| / m := by
    rw [← Real.log_div hx.ne' hy.ne']
    calc
      Real.log (x / y) ≤ x / y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by
        field_simp [hy.ne']
        <;> ring
      _ ≤ |x - y| / m := by
        apply (div_le_div_iff₀ hy hm).2
        calc
          (x - y) * m ≤ |x - y| * m :=
            mul_le_mul_of_nonneg_right (le_abs_self (x - y)) hm.le
          _ ≤ |x - y| * y :=
            mul_le_mul_of_nonneg_left hmy (abs_nonneg (x - y))
  have hReverse :
      Real.log y - Real.log x ≤ |y - x| / m := by
    rw [← Real.log_div hy.ne' hx.ne']
    calc
      Real.log (y / x) ≤ y / x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hy hx)
      _ = (y - x) / x := by
        field_simp [hx.ne']
        <;> ring
      _ ≤ |y - x| / m := by
        apply (div_le_div_iff₀ hx hm).2
        calc
          (y - x) * m ≤ |y - x| * m :=
            mul_le_mul_of_nonneg_right (le_abs_self (y - x)) hm.le
          _ ≤ |y - x| * x :=
            mul_le_mul_of_nonneg_left hmx (abs_nonneg (y - x))
  apply abs_le.mpr
  constructor
  · rw [abs_sub_comm] at hReverse
    linarith
  · exact hUpper

/-- The pointwise vacuum target-update ratio has the volume-uniform lower floor
exp(-8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_exp_neg_eight_mul_le_update_ratio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-8 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target g) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B := by
  have hB :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hH :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
      H N hN beta hbeta B target (B target) g
  have hH' :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update B target g) := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    ] using hH
  apply (le_div_iff₀ hB).2
  calc
    Real.exp (-8 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B ≤
      Real.exp (-8 * beta) *
        (Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update B target g)) :=
      mul_le_mul_of_nonneg_left hH' (Real.exp_pos _).le
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update B target g) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp

/-- The base posterior target expectation inherits the same lower floor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_exp_neg_eight_mul_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-8 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
        H N hN beta hbeta B target g := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_exp_neg_eight_mul_le_update_ratio
      H N hN beta hbeta B target g

/-- Under remote source separation, the source-re-tilted target expectation
also inherits the same lower floor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_exp_neg_eight_mul_le
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
    Real.exp (-8 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
        H N hN beta hbeta B target source sourceValue g := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
      H N hN beta hbeta B target source sourceValue g hNe hRemote]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_exp_neg_eight_mul_le_update_ratio
      H N hN beta hbeta (Function.update B source sourceValue) target g

/-- Uniform ordinary expectation discrepancy under the source-local re-tilt. -/
def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (epsilon : ℝ) : Prop :=
  ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
        H N hN beta hbeta B target g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
        H N hN beta hbeta B target source sourceValue g| ≤ epsilon

/-- An ordinary expectation discrepancy epsilon gives logarithmic response
epsilon / exp(-8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetLogResponseBound_of_expectationResponse
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
    (epsilon : ℝ)
    (hResponse :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
        H N hN beta hbeta B target source sourceValue epsilon) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLogResponseBound
      H N hN beta hbeta B target source sourceValue
      (epsilon / Real.exp (-8 * beta)) := by
  intro g
  let x :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
      H N hN beta hbeta B target g
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
      H N hN beta hbeta B target source sourceValue g
  let m : ℝ := Real.exp (-8 * beta)
  have hm : 0 < m := by
    dsimp [m]
    exact Real.exp_pos _
  have hmx : m ≤ x := by
    simpa [m, x] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_exp_neg_eight_mul_le
        H N hN beta hbeta B target g
  have hmy : m ≤ y := by
    simpa [m, y] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_exp_neg_eight_mul_le
        H N hN beta hbeta B target source sourceValue g hNe hRemote
  have hLog :
      |Real.log x - Real.log y| ≤ |x - y| / m :=
    abs_log_sub_log_le_abs_sub_div_lower hm hmx hmy
  have hDisc : |x - y| ≤ epsilon := by
    simpa [x, y] using hResponse g
  calc
    |Real.log x - Real.log y| ≤ |x - y| / m := hLog
    _ ≤ epsilon / m := by
      apply (div_le_div_iff₀ hm hm).2
      exact mul_le_mul_of_nonneg_right hDisc hm.le

/-- Consequently, an ordinary remote-source posterior expectation discrepancy
epsilon gives the complete target-fiber TV receiver with explicit log radius
epsilon / exp(-8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_remoteSource_posteriorExpectationResponse
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
    (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hResponse :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
        H N hN beta hbeta B target source sourceValue epsilon) :
    (2 : ℝ)⁻¹ *
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left B target g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left
                (Function.update B source sourceValue) target g|
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      (Real.exp (2 * (epsilon / Real.exp (-8 * beta))) - 1) /
        (Real.exp (2 * (epsilon / Real.exp (-8 * beta))) + 1) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_remoteSource_posteriorLogResponse
      H N hN beta hbeta left B target source sourceValue
      hNe hRemote
      (epsilon / Real.exp (-8 * beta))
      (div_nonneg hepsilon (Real.exp_pos _).le)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetLogResponseBound_of_expectationResponse
      H N hN beta hbeta B target source sourceValue
      hNe hRemote epsilon hResponse

end

end MathlibAnalytic
end MGAP4D
