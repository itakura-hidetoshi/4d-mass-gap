import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialCrossRatioTV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Tactic

/-!
# Continuous physical-vacuum complete one-link ground-state fiber log weight

The ground-state right-boundary one-link fiber contains two positive factors
that depend on the inserted target value:

* the literal one-slab Wilson kernel;
* the canonical continuous physical vacuum on the updated right boundary.

The left vacuum and the transfer-norm normalization are constant along the
target fiber and disappear after normalization.  This file therefore packages
the complete variable log weight

  log K(left, right[target := g]) + log Omega(right[target := g]).

Both factors are strictly positive and continuous, so this is a genuine
continuous real log weight on compact SU(N).  Its normalized exponential
density is exactly the normalized product K * Omega.  Consequently the generic
cross-ratio theorem of PR #5149 gives the sharp half-L1 / total-variation
bound without any separate estimate of a normalization denominator.

This is still a pointwise continuous-vacuum fiber statement.  Identification
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

/-- The complete variable log weight of the continuous-vacuum ground-state
right target-link fiber.  Constants independent of the target value are
deliberately omitted because normalization cancels them exactly. -/
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
  let updated :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N right target g
  Real.log
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left updated) +
    Real.log
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta updated)

/-- The complete continuous-vacuum target-fiber log weight is continuous in
the inserted group value. -/
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
  let update :=
    fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N right target g
  have hUpdate : Continuous update := by
    simpa [update] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N right target
  have hPair : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => (left, update g)) :=
    continuous_const.prodMk hUpdate
  have hKernel : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left (update g)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp hPair
  have hKernelLog : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Real.log
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left (update g))) := by
    exact hKernel.log (fun g =>
      ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H N beta left (update g)))
  have hVacuum : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (update g)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).comp hUpdate
  have hVacuumLog : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Real.log
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (update g))) := by
    exact hVacuum.log (fun g =>
      ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta (update g)))
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight,
    update
  ] using hKernelLog.add hVacuumLog

/-- Exponentiating the complete log weight recovers exactly the variable
one-slab-kernel times continuous-vacuum factor. -/
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
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N right target g) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N right target g) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
  rw [Real.exp_add]
  rw [Real.exp_log
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta left
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N right target g))]
  rw [Real.exp_log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N right target g))]

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

/-- The normalized density is literally the normalized product of the raw
one-slab kernel and the continuous physical vacuum. -/
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
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N right target g) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N right target g)) /
        ∫ h : Matrix.specialUnitaryGroup (Fin N) ℂ,
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta left
              (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
                H N right target h) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta
              (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
                H N right target h))
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
