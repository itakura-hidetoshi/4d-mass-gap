import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointMeasureIdentification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkOriginalCoordinateMarkovIdentity
import Mathlib.Tactic

/-!
# P4-Q2-AV: original physical Wilson conditional fibers versus continuous vacuum

AU established that the EXACT original physical Wilson ground-state joint
measure equals the canonical continuous-vacuum one-slab Wilson joint measure.
The density equality holds pair-Haar-almost everywhere, NOT at all values of
the old arbitrary Haar-L² vacuum representative.

This file transports that measure-level identification through the EXISTING
right-boundary target-link × off-target measurable equivalence and the
EXISTING true Markov-disintegration coordinate carrier.

For Haar-almost every (left boundary, off-target right-boundary context),
the original split target-link fiber weight agrees target-Haar-almost
everywhere with the actual continuous-vacuum Wilson joint weight.
Consequently the literal original normalized ground-state target-fiber
MEASURE equals the exactly normalized continuous-physical-vacuum fiber
MEASURE for almost every outer context.

No exceptional fixed fiber is upgraded to pointwise equality; no new
regular conditional distribution is claimed beyond the already-proved
Markov disintegration. The target fiber lives on the ORIGINAL singleton
right-link SU(N) product-Haar carrier. The global Yang–Mills gap and
spacing-uniform Dirichlet lower bounds remain open.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4AVGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AVCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AVSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AVMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AVBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AVLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AVTargetLinks (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- A generic normalization stability theorem: Haar-almost everywhere
equality of arbitrary ENNReal weights entails exact equality of their
Doob-normalized fiber measures, including at any exceptional
normalization mass 0 or infinity. No pointwise fiber equality is used. -/
theorem p4Q2AV_doobWeightedMeasure_eq_of_ae_eq
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w v : X → ENNReal)
    (h : w =ᵐ[mu] v) :
    doobWeightedMeasure mu w = doobWeightedMeasure mu v := by
  have hm : doobWeightMass mu w = doobWeightMass mu v := by
    exact lintegral_congr_ae h
  unfold doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  unfold doobWeightedDensity
  rw [hx, hm]

/-- The continuous physical Wilson ground-state joint density, restricted
to the SAME original split target × off-target right-boundary carrier,
at any given left boundary and retained off-target configuration. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ENNReal :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
      H N hN beta hbeta
      (left, (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
          (targetCfg, retained)))

/-- This canonical continuous fiber is the normalized exact positive
Wilson physical joint density on the same original singleton-target
Haar product measure used in the established disintegration. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
        H N hN beta hbeta left target targetCfg retained)

/-- Fubini transport of the AU Haar-pair density equality across the actual
original target/off-target split. Both exceptional sets are retained.
This proves pointwise equality on neither EVERY context nor EVERY fiber. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalJointSplitTargetDensity_ae_eq_continuous
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
      ∀ᵐ targetCfg ∂(Measure.pi (fun _ :
        PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
          H N hN beta hbeta ctx.1 target (targetCfg, ctx.2) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
          H N hN beta hbeta ctx.1 target targetCfg ctx.2 := by
  classical
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let muTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  have hCoord : MeasurePreserving coord ((mu.prod muOff).prod muTarget) (mu.prod mu) := by
    simpa [coord, mu, muOff, muTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H N target)
  have hPair : (fun z =>
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z)) =ᵐ[mu.prod mu]
      (fun z => ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
          H N hN beta hbeta z)) := by
    filter_upwards
      [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuous
        H N hN beta hbeta] with z hz
    exact congrArg ENNReal.ofReal hz
  have hSplit :
      (fun z =>
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta (coord z))) =ᵐ[((mu.prod muOff).prod muTarget)]
      (fun z => ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
          H N hN beta hbeta (coord z))) := by
    simpa [Function.comp_def] using hCoord.quasiMeasurePreserving.ae_eq hPair
  have hSections : ∀ᵐ ctx ∂(mu.prod muOff), ∀ᵐ targetCfg ∂muTarget,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta ctx.1 target (targetCfg, ctx.2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
        H N hN beta hbeta ctx.1 target targetCfg ctx.2 := by
    simpa [coord,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity]
      using (Measure.ae_ae_of_ae_prod hSplit)
  simpa [mu, muOff, muTarget] using hSections

/-- The ACTUAL original physical Wilson split-target normalized conditional
measure equals the canonical continuous physical-ground-state conditional
measure for Haar-almost every outer left/off-target context. This is an
unconditional (except the correct AE quantifiers) MEASURE equality, not
an identification of old quotient representatives at fixed exceptional fibers. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_eq_continuous
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2 =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2 := by
  let muTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have hWeight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalJointSplitTargetDensity_ae_eq_continuous
      H N hN beta hbeta target
  filter_upwards [hWeight] with ctx hctx
  have hEq := p4Q2AV_doobWeightedMeasure_eq_of_ae_eq
    muTarget
    (fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta ctx.1 target (targetCfg, ctx.2))
    (fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
        H N hN beta hbeta ctx.1 target targetCfg ctx.2)
    hctx
  simpa [muTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure]
    using hEq

end
end MathlibAnalytic
end MGAP4D
