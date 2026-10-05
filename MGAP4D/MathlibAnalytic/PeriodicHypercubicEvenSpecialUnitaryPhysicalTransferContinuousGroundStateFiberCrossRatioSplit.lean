import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatio
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

/-!
# Split the continuous ground-state fiber cross-ratio

The complete continuous ground-state target-fiber weight is

  K(left, right[target := g]) * Omega(right[target := g]).

The exact one-slab target update factorization writes the kernel factor as

  localFactor(left, right, target, g) * K(left, right).

In the four-point cross-ratio comparing two right environments and two target
values, the baseline factors K(left,right_i) cancel.  Therefore the complete
log-weight cross-difference is exactly the sum of

* a target-local Wilson log-factor cross-difference;
* a continuous-vacuum log-weight cross-difference.

This file formalizes that algebraic separation and composes it with the sharp
normalized half-L1/TV theorem from PR #5149/#5150.

The next locality theorem only has to show that the first term vanishes for a
remote source perturbation and control the second term quantitatively.  No such
distance-decay estimate is asserted here.  No update-time/Euclidean-time
identification, H1-D5 exact descent, or complete Yang--Mills mass-gap claim is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance groundStateFiberCrossRatioSplitTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateFiberCrossRatioSplitCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateFiberCrossRatioSplitSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateFiberCrossRatioSplitMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateFiberCrossRatioSplitBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Logarithm of the exact target-local Wilson factor appearing when the
selected right-boundary link is updated. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
    (H N : ℕ)
    (beta : ℝ)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.log
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta left right target g)

/-- Logarithm of the continuous physical vacuum evaluated on the updated right
boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta (Function.update right target g))

/-- The complete continuous ground-state target-fiber weight factors into the
exact target-local Wilson factor, the baseline one-slab kernel, and the updated
continuous vacuum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_eq_localFactor_mul_baseKernel_mul_vacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta left right target g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left right *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update right target g) := by
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left (Function.update right target g) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update right target g) =
    _
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta left right target g]

/-- Pointwise log decomposition of the complete fiber weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_eq_localFactorLog_add_baseKernelLog_add_vacuumLog
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right target g +
        Real.log
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left right) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right target g := by
  have hLocal :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta left right target g ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta left right target g)
  have hKernel :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left right ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta left right)
  have hVacuum :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update right target g) ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (Function.update right target g))
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_eq_localFactor_mul_baseKernel_mul_vacuum
      H N hN beta hbeta left right target g,
    Real.log_mul (mul_ne_zero hLocal hKernel) hVacuum,
    Real.log_mul hLocal hKernel]

/-- In the four-point cross-difference the baseline one-slab kernel terms
cancel exactly.  What remains is the target-local Wilson contribution plus the
continuous-vacuum contribution. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossDifference_eq_localFactor_add_vacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right₁ target u -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right₂ target u) -
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right₁ target v -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right₂ target v) =
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₁ target u -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₂ target u) -
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₁ target v -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₂ target v)) +
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₁ target u -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₂ target u) -
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₁ target v -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₂ target v)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_eq_localFactorLog_add_baseKernelLog_add_vacuumLog
      H N hN beta hbeta left right₁ target u,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_eq_localFactorLog_add_baseKernelLog_add_vacuumLog
      H N hN beta hbeta left right₂ target u,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_eq_localFactorLog_add_baseKernelLog_add_vacuumLog
      H N hN beta hbeta left right₁ target v,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_eq_localFactorLog_add_baseKernelLog_add_vacuumLog
      H N hN beta hbeta left right₂ target v]
  ring

/-- Separate cross-ratio radii for the target-local Wilson factor and the
continuous vacuum add to a valid radius for the complete ground-state fiber
log weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_of_split
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (Rlocal Rvacuum : ℝ)
    (hLocal :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₁ target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₂ target)
        Rlocal)
    (hVacuum :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₁ target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₂ target)
        Rvacuum) :
    ContinuousNormalizedExpCrossRatioBound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right₁ target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right₂ target)
      (Rlocal + Rvacuum) := by
  intro u v
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossDifference_eq_localFactor_add_vacuum
      H N hN beta hbeta left right₁ right₂ target u v]
  exact add_le_add (hLocal u v) (hVacuum u v)

/-- The split cross-ratio estimate feeds directly into the sharp normalized
half-L1/total-variation estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_splitCrossRatio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right₁ right₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (Rlocal Rvacuum : ℝ)
    (hRlocal : 0 ≤ Rlocal)
    (hRvacuum : 0 ≤ Rvacuum)
    (hLocal :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₁ target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
          H N beta left right₂ target)
        Rlocal)
    (hVacuum :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₁ target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right₂ target)
        Rvacuum) :
    (2 : ℝ)⁻¹ *
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left right₁ target g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left right₂ target g|
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      (Real.exp (Rlocal + Rvacuum) - 1) /
        (Real.exp (Rlocal + Rvacuum) + 1) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_crossRatio
      H N hN beta hbeta left right₁ right₂ target
      (Rlocal + Rvacuum)
      (add_nonneg hRlocal hRvacuum)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_of_split
      H N hN beta hbeta left right₁ right₂ target
      Rlocal Rvacuum hLocal hVacuum

end

end MathlibAnalytic
end MGAP4D
