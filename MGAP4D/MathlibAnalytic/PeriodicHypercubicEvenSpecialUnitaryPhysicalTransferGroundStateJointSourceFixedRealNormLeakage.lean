import MGAP4D.MathlibAnalytic.RealNormENNRealSquaredBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedJointLeakage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileSourceFixedLeakage

/-!
# Exact real source-fixed leakage and bounded-core forcing

Starting from #4932, set A(source,target) = (2 : ENNReal)^(-1) * Gamma(source,target)
and k(source,target) = sqrt(A(source,target).toReal). The existing #4927 cutoff
proves A is finite. The generic finite-ENNReal conversion then gives the actual
joint norm estimate, including zero residuals, without another representative
selection, pair normalization, stationarity argument or numerator identification.

The source-fixed specialization and the #4924/#4923 receivers are reused to
obtain a genuine one-step source-residual cost and an actual cyclic budget.
The coefficient still contains K_pin(target,source), in that literal order.
Domination by K_phys(source,target), the physical Schur recurrence and strict
renewal contraction are NOT established by this file.
-/

namespace MGAP4D.MathlibAnalytic

open scoped ENNReal

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Core" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta

/-- The exact iid half-normalization. No source/target reversal is performed. -/
def jointLeakageHalfOrderedCoefficient (s : ℝ) (source target : Link) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
      H N hN s beta hbeta source target

/-- Reuse the existing ordered coefficient's finiteness on the same cutoff. -/
theorem jointLeakageHalfOrderedCoefficient_ne_top
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source target : Link) :
    jointLeakageHalfOrderedCoefficient H N hN beta hbeta s source target ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient_ne_top
      N hN s hs beta hbeta hcut H source target)

/-- Real norm coefficient. Its use in estimates below explicitly requires
finiteness; `toReal` alone is not a valid estimate at infinity. -/
def jointLeakageNormCoefficient (s : ℝ) (source target : Link) : ℝ :=
  Real.sqrt (jointLeakageHalfOrderedCoefficient H N hN beta hbeta s source target).toReal

theorem jointLeakageNormCoefficient_nonneg (s : ℝ) (source target : Link) :
    0 ≤ jointLeakageNormCoefficient H N hN beta hbeta s source target :=
  Real.sqrt_nonneg _

/-- The exact real square keeps the half-factor inside the coefficient. -/
theorem jointLeakageNormCoefficient_sq (s : ℝ) (source target : Link) :
    (jointLeakageNormCoefficient H N hN beta hbeta s source target) ^ 2 =
      (jointLeakageHalfOrderedCoefficient H N hN beta hbeta s source target).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

/-- The actual source update of a bounded-core vector satisfies the genuine
joint norm bound. No positivity of its target residual is assumed. -/
theorem sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source : Link) (f : JL2) (hf : f ∈ Core) :
    ∀ target : Link, target ≠ source →
      ‖P target (P source f) - P source (P target (P source f))‖ ≤
        jointLeakageNormCoefficient H N hN beta hbeta s source target *
          ‖P source f - P target (P source f)‖ := by
  intro target hne
  exact norm_le_sqrt_toReal_mul_norm_of_ofReal_norm_sq_le
    (jointLeakageHalfOrderedCoefficient H N hN beta hbeta s source target)
    (jointLeakageHalfOrderedCoefficient_ne_top H N hN beta hbeta s hs hcut source target)
    (P target (P source f) - P source (P target (P source f)))
    (P source f - P target (P source f))
    (sourceUpdate_jointLeakage_norm_sq_le_half_orderedCoefficient
      H N hN beta hbeta s hs hcut source f hf target hne)

/-- The exact input shape required by the existing source-fixed receiver.
Specialize the actual-update theorem at f = g and rewrite P_source g = g. -/
theorem jointLeakage_norm_le_orderedNormCoefficient_of_sourceFixed
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source target : Link) (hne : target ≠ source)
    (g : JL2) (hg : g ∈ Core) (hFixed : P source g = g) :
    ‖P target g - P source (P target g)‖ ≤
      jointLeakageNormCoefficient H N hN beta hbeta s source target * ‖g - P target g‖ := by
  simpa only [hFixed] using
    sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
      H N hN beta hbeta s hs hcut source g hg target hne

/-- The genuine one-step source-residual cost on the bounded core. Hilbert
duality is imported from #4924; it is not reproved and no cardinality factor occurs. -/
theorem sourceUpdate_targetResidual_norm_le_add_sourceResidual
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source : Link) (f : JL2) (hf : f ∈ Core) :
    ∀ target : Link, target ≠ source →
      ‖P source f - P target (P source f)‖ ≤
        ‖f - P target f‖ + jointLeakageNormCoefficient H N hN beta hbeta s source target *
          ‖f - P source f‖ := by
  intro target hne
  exact realHilbertProjection_targetResidual_norm_le_add_sourceResidual_of_leakage
    (P target) (P source)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
      H N hN beta hbeta target)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
      H N hN beta hbeta source)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
      H N hN beta hbeta target)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
      H N hN beta hbeta source)
    (jointLeakageNormCoefficient H N hN beta hbeta s source target)
    (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target) f
    (sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
      H N hN beta hbeta s hs hcut source f hf target hne)

end GroundStateSourceFixedPairEnergy

open GroundStateSourceFixedPairEnergy

/-- Actual cyclic bounded-core budget with the exact ordered norm coefficient.
This discharges the analytic leakage premise of #4924, but does not identify
this coefficient with the physical Schur envelope. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicOrderedNormSourceResidualBudget
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta)
    (hSplit : (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      pre ++ target :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        (fun source x => jointLeakageNormCoefficient H N hN beta hbeta s source.1 target.1 *
          ‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color source x‖)
        (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color) pre f)) := by
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
    H N hN beta hbeta color
  let K := fun (source target : PeriodicHypercubicEvenFixedSpatialColorLink H color) =>
    jointLeakageNormCoefficient H N hN beta hbeta s source.1 target.1
  apply periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicSourceResidualBudget_of_sourceFixedLeakage
    H N hN beta hbeta color pre suffix target f hf hSplit K
    (fun source => jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source.1 target.1)
  change ∀ (source : PeriodicHypercubicEvenFixedSpatialColorLink H color),
    source.1 ≠ target.1 →
    ∀ (g : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      g ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta →
      P source g = g →
      ‖P target g - P source (P target g)‖ ≤ K source target * ‖g - P target g‖
  intro source hne g hg hFixed
  simpa only [P, K,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
    jointLeakage_norm_le_orderedNormCoefficient_of_sourceFixed
      H N hN beta hbeta s hs hcut source.1 target.1 (Ne.symm hne) g hg hFixed

end

end MGAP4D.MathlibAnalytic
