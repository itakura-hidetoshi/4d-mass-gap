import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteOneLinkSweepInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceSet
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepVectorTelescoping
import Mathlib.Tactic

/-!
# Exact bounded carrier for one actual cyclic source update

Fix a canonical target split

  canonicalList = pre ++ target :: suffix

and then split the exact between-visits list at one actual source

  suffix ++ pre = before ++ source :: after.

Starting immediately after the first target projection, this file chooses
bounded concrete representatives before and after that source update and proves

  afterL2 = Q_source beforeL2.

The same cyclic source-set theorem from PR #4899 discharges

  source != target

after forgetting the fixed-color subtype.

Thus a single actual step of the cyclic trajectory is now on the concrete
carrier required by the source-update semantic and quantitative machinery.

No commutativity, reordering, cardinality estimate, response symmetry, or
pointwise evaluation of an arbitrary L2 quotient representative is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance cyclicSourceStepCarrierSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance cyclicSourceStepCarrierSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance cyclicSourceStepCarrierSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance cyclicSourceStepCarrierSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance cyclicSourceStepCarrierSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance cyclicSourceStepCarrierSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One actual cyclic source update admits bounded concrete representatives on
both sides, with exact Hilbert transition by the genuine source conditional
expectation and with the off-diagonal geometry discharged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStep_exists_boundedRepresentative_pair
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix before after :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hCanonicalSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hFresh : target ∉ pre)
    (hCyclicSplit :
      suffix ++ pre = before ++ source :: after)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (Fbefore :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hFbefore : StronglyMeasurable Fbefore)
      (boundBefore : ℝ)
      (hboundBefore : ∀ z, ‖Fbefore z‖ ≤ boundBefore)
      (Fafter :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hFafter : StronglyMeasurable Fafter)
      (boundAfter : ℝ)
      (hboundAfter : ∀ z, ‖Fafter z‖ ≤ boundAfter),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore =
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          before
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target
            (realHilbertProjectionSweep
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color)
              pre f)) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta Fafter hFafter boundAfter hboundAfter =
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          (before ++ [source])
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target
            (realHilbertProjectionSweep
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color)
              pre f)) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta Fafter hFafter boundAfter hboundAfter =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) ∧
      source.1 ≠ target.1 := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let x0 :=
    P target
      (realHilbertProjectionSweep P pre f)
  have hPre :
      realHilbertProjectionSweep P pre f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color pre f hf
  have hStart :
      x0 ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    dsimp [x0]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2_mem_boundedConcreteCore
        H N hN beta hbeta color target
        (realHilbertProjectionSweep P pre f) hPre
  have hBefore :
      realHilbertProjectionSweep P before x0 ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color before x0 hStart
  have hAfter :
      realHilbertProjectionSweep P (before ++ [source]) x0 ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color (before ++ [source]) x0 hStart
  rcases hBefore with
    ⟨Fbefore, hFbefore, boundBefore, hboundBefore, hRepBefore⟩
  rcases hAfter with
    ⟨Fafter, hFafter, boundAfter, hboundAfter, hRepAfter⟩
  have hStep :
      realHilbertProjectionSweep P (before ++ [source]) x0 =
        P source (realHilbertProjectionSweep P before x0) := by
    rw [realHilbertProjectionSweep_append]
    simp [realHilbertProjectionSweep]
  have hsourceMem : source ∈ suffix ++ pre := by
    rw [hCyclicSplit]
    simp
  have hne :
      source.1 ≠ target.1 :=
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
      H color pre suffix target source hCanonicalSplit hFresh hsourceMem
  refine
    ⟨Fbefore, hFbefore, boundBefore, hboundBefore,
      Fafter, hFafter, boundAfter, hboundAfter, ?_, ?_, ?_, hne⟩
  · simpa [P, x0] using hRepBefore
  · simpa [P, x0] using hRepAfter
  · calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta Fafter hFafter boundAfter hboundAfter =
        realHilbertProjectionSweep P (before ++ [source]) x0 :=
          hRepAfter
      _ = P source (realHilbertProjectionSweep P before x0) := hStep
      _ =
        P source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) := by
          rw [hRepBefore]
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) := by
          rfl

end

end MGAP4D.MathlibAnalytic
