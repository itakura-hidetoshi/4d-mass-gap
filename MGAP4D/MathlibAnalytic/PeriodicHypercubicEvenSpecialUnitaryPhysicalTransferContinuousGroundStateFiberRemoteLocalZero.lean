import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatioSplit
import Mathlib.Tactic

/-!
# Remote-source vanishing of the local ground-state fiber cross-ratio term

PR #5152 splits the complete continuous ground-state one-link cross-ratio into

* a target-local Wilson factor;
* a continuous physical-vacuum factor.

This file closes the first term for a genuinely remote right-boundary source
link.  Two intrinsic spatial links are declared plaquette-local when one
intrinsic spatial plaquette touches both.  If the source is distinct from the
target and is not plaquette-local to it, then changing only that source link

* leaves the stored target coordinate unchanged;
* leaves every target-touching plaquette holonomy unchanged;
* therefore leaves the exact target-local Wilson factor unchanged pointwise;
* hence gives local log cross-ratio radius exactly zero.

Consequently the complete normalized target-fiber TV estimate depends only on
the continuous-vacuum cross-ratio radius.

No decay estimate for that vacuum radius is asserted here.  No heat-bath-time /
Euclidean-time identification, H1-D5 exact descent, or complete Yang--Mills
mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance groundStateFiberRemoteLocalZeroTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateFiberRemoteLocalZeroCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateFiberRemoteLocalZeroSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateFiberRemoteLocalZeroMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateFiberRemoteLocalZeroBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateFiberRemoteLocalZeroSpatialPlaquetteFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  Fintype.ofFinite _

/-- Intrinsic spatial Wilson-plaquette locality: two spatial links are local if
one intrinsic spatial plaquette touches both. -/
def periodicHypercubicEvenSpatialSlicePlaquetteLocal
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : Prop :=
  ∃ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
    periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target ∧
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source

/-- If source is not spatial-plaquette-local to target, every plaquette in the
target touching family misses source. -/
theorem periodicHypercubicEvenSpatialSlice_not_touches_source_of_not_plaquetteLocal
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hp : p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target) :
    ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source := by
  intro hpSource
  apply hRemote
  exact
    ⟨p,
      (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff
        H target p).mp hp,
      hpSource⟩

/-- Updating a remote right-boundary source link leaves the exact target-local
one-slab Wilson factor unchanged for every inserted target value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_source_eq_of_not_plaquetteLocal
    (H N : ℕ)
    (beta : ℝ)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta left (Function.update right source sourceValue) target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta left right target g := by
  classical
  have hTargetValue :
      Function.update right source sourceValue target = right target := by
    simp [Function.update, Ne.symm hNe]
  have hBaseHolonomy :
      ∀ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update right source sourceValue) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy right p := by
    intro p hp
    have hpNotSource :
        ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source :=
      periodicHypercubicEvenSpatialSlice_not_touches_source_of_not_plaquetteLocal
        H target source hRemote p hp
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    ] using
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
        H N right source sourceValue p hpNotSource)
  have hUpdatedHolonomy :
      ∀ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update
              (Function.update right source sourceValue) target g) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update right target g) p := by
    intro p hp
    have hpNotSource :
        ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source :=
      periodicHypercubicEvenSpatialSlice_not_touches_source_of_not_plaquetteLocal
        H target source hRemote p hp
    have hHolonomy :
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update
              (Function.update right target g) source sourceValue) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update right target g) p := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      ] using
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H N (Function.update right target g) source sourceValue p hpNotSource)
    rw [Function.update_comm hNe sourceValue g right]
    exact hHolonomy
  have hSum :
      (∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update
                (Function.update right source sourceValue) target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update right source sourceValue) p))) =
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update right target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy right p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hUpdatedHolonomy p hp, hBaseHolonomy p hp]
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
  rw [hTargetValue, hSum]

/-- The corresponding target-local log weight is pointwise unchanged by a
remote source update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight_update_source_eq_of_not_plaquetteLocal
    (H N : ℕ)
    (beta : ℝ)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
        H N beta left (Function.update right source sourceValue) target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
        H N beta left right target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_source_eq_of_not_plaquetteLocal
      H N beta left right target source sourceValue hNe hRemote g]

/-- A remote source update gives exact zero cross-ratio radius for the
target-local Wilson contribution. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight_crossRatioBound_zero_of_not_plaquetteLocal
    (H N : ℕ)
    (beta : ℝ)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    ContinuousNormalizedExpCrossRatioBound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
        H N beta left right target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight
        H N beta left (Function.update right source sourceValue) target)
      0 := by
  intro u v
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight_update_source_eq_of_not_plaquetteLocal
      H N beta left right target source sourceValue hNe hRemote u,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight_update_source_eq_of_not_plaquetteLocal
      H N beta left right target source sourceValue hNe hRemote v]
  norm_num

/-- Once source is remote from target, any cross-ratio radius for the
continuous-vacuum factor is already a complete ground-state fiber cross-ratio
radius: the local Wilson contribution is exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_of_remoteSource_vacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (R : ℝ)
    (hVacuum :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta (Function.update right source sourceValue) target)
        R) :
    ContinuousNormalizedExpCrossRatioBound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left (Function.update right source sourceValue) target)
      R := by
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkLocalFactorLogWeight_crossRatioBound_zero_of_not_plaquetteLocal
      H N beta left right target source sourceValue hNe hRemote
  simpa using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_of_split
      H N hN beta hbeta left right
        (Function.update right source sourceValue) target
        0 R hLocal hVacuum)

/-- The sharp normalized target-fiber half-L1/TV estimate for a remote source
therefore depends only on the continuous-vacuum cross-ratio radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_remoteSource_vacuumCrossRatio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hVacuum :
      ContinuousNormalizedExpCrossRatioBound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta right target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkVacuumLogWeight
          H N hN beta hbeta (Function.update right source sourceValue) target)
        R) :
    (2 : ℝ)⁻¹ *
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left right target g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
              H N hN beta hbeta left
                (Function.update right source sourceValue) target g|
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_crossRatio
      H N hN beta hbeta left right
        (Function.update right source sourceValue) target R hR
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_of_remoteSource_vacuum
      H N hN beta hbeta left right target source sourceValue
      hNe hRemote R hVacuum

end

end MathlibAnalytic
end MGAP4D
