import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialCrossRatioTV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferProjectedTail
import Mathlib.Tactic

/-!
# Continuous physical-vacuum complete one-link ground-state fiber log weight

The ground-state right-boundary one-link fiber contains two positive factors
that depend on the inserted target value:

* the literal one-slab Wilson kernel;
* the canonical continuous physical vacuum on the updated right boundary.

The left vacuum and the transfer-norm normalization are constant along the
target fiber and disappear after normalization.  We first package the complete
positive variable weight

  W(g) = K(left, right[target := g]) * Omega(right[target := g]),

and only then define the complete log weight as log W(g).  This presentation
keeps Lean elaboration small: continuity is proved once for the positive
product, and continuity of the logarithm follows from strict positivity.

The normalized exponential density of log W is exactly W / integral W.  Hence
the generic cross-ratio theorem of PR #5149 supplies the sharp half-L1 /
total-variation bound without any separate normalization-denominator estimate.

This remains a pointwise continuous-vacuum fiber statement.  Identification
with the historical genuine joint measure, whose definition uses the original
L2 representative, is intentionally left to the next bridge.  No Euclidean
time identification, H1-D5 exact descent, or complete Yang--Mills mass-gap
claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance continuousGroundStateFiberLogWeightTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousGroundStateFiberLogWeightCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousGroundStateFiberLogWeightSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousGroundStateFiberLogWeightMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousGroundStateFiberLogWeightBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Right spatial boundary with the selected target link replaced by g. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
    (H N : ℕ)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N right target g

/-- The target-link replacement map is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight_continuous
    (H N : ℕ)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
        H N right target) := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
  ] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
      H N right target

/-- Complete positive variable weight of the continuous-vacuum ground-state
right target-link fiber.  Factors constant along the target fiber are omitted. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
        H N right target g) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
        H N right target g)

/-- The complete target-fiber weight is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right target) := by
  have hUpdate :
      Continuous
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
          H N right target) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight_continuous
      H N right target
  have hKernel : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
            H N right target g)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp₂ continuous_const hUpdate
  have hVacuum : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
            H N right target g)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).comp hUpdate
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
  ] using hKernel.mul hVacuum

/-- The complete target-fiber weight is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
        H N right target g))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
        H N right target g))

/-- Complete log weight of the continuous-vacuum target fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
      H N hN beta hbeta left right target g)

/-- The complete continuous-vacuum target-fiber log weight is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right target) := by
  have hWeight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_continuous
      H N hN beta hbeta left right target
  have hNonzero :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left right target g ≠ 0 := fun g =>
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_pos
        H N hN beta hbeta left right target g)
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
  ] using hWeight.log hNonzero

/-- Exponentiating the complete log weight recovers the complete positive
target-fiber weight exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right target g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
  exact Real.exp_log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_pos
      H N hN beta hbeta left right target g)

/-- Normalized Haar density of the continuous-vacuum ground-state right
target-link fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  continuousNormalizedExp
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H N hN beta hbeta left right target)
    g

/-- The normalized density is literally W divided by its Haar integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
        H N hN beta hbeta left right target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left right target g /
        ∫ h : Matrix.specialUnitaryGroup (Fin N) ℂ,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
            H N hN beta hbeta left right target h
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
    continuousNormalizedExp
    continuousExpPartition
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_exp]
  congr 1
  apply integral_congr_ae
  filter_upwards with h
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_exp
      H N hN beta hbeta left right target h

/-- The continuous-vacuum normalized target-fiber density is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
        H N hN beta hbeta left right target) := by
  exact
    continuous_continuousNormalizedExp
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_continuous
        H N hN beta hbeta left right target)

/-- A complete-log-weight cross-ratio radius gives the sharp total-variation
bound between two continuous-vacuum ground-state target fibers with the same
left boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_crossRatio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hCross :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right₁ target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right₂ target)
        R) :
    (2 : ℝ)⁻¹ *
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left right₁ target g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left right₂ target g|
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  exact
    continuousNormalizedExp_halfL1_le_of_crossRatio
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right₁ target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right₂ target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_continuous
        H N hN beta hbeta left right₁ target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_continuous
        H N hN beta hbeta left right₂ target)
      R hR hCross

end

end MathlibAnalytic
end MGAP4D
