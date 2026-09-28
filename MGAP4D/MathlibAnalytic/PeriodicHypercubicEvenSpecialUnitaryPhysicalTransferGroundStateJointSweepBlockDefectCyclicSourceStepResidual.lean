import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepCarrier
import Mathlib.Tactic

/-!
# Exact cyclic source residual as the actual stage residual

PR #4906 places one actual cyclic source update on bounded concrete carriers:

  afterL2 = Q_source beforeL2.

This file identifies the genuine source conditional-expectation residual of the
before representative with the exact Hilbert stage residual of that cyclic
source update.

Thus the residual appearing on the right side of the existing quantitative
source-update bounds is not merely comparable with, but exactly equal to, the
actual trajectory residual.  Both the vector equality and the squared-norm
identity are recorded.

No approximation, triangle inequality, response symmetry, or new coefficient
is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance cyclicSourceStepResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance cyclicSourceStepResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance cyclicSourceStepResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance cyclicSourceStepResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance cyclicSourceStepResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance cyclicSourceStepResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For one actual cyclic source step, choose bounded representatives such that
its genuine source CondExpL2 residual is exactly the stage residual vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStep_exists_boundedRepresentative_sourceResidual_eq_stageResidual
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
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source.1
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) =
        realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            before
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color target
              (realHilbertProjectionSweep
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                  H N hN beta hbeta color)
                pre f)) -
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
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source.1
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore)‖ ^ 2 =
        ‖realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            before
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color target
              (realHilbertProjectionSweep
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                  H N hN beta hbeta color)
                pre f)) -
          realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            (before ++ [source])
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color target
              (realHilbertProjectionSweep
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                  H N hN beta hbeta color)
                pre f))‖ ^ 2 ∧
      source.1 ≠ target.1 := by
  obtain
    ⟨Fbefore, hFbefore, boundBefore, hboundBefore,
      Fafter, hFafter, boundAfter, hboundAfter,
      hRepBefore, hRepAfter, hStep, hne⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStep_exists_boundedRepresentative_pair
      H N hN beta hbeta color pre suffix before after target source
      hCanonicalSplit hFresh hCyclicSplit f hf
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let x0 :=
    P target (realHilbertProjectionSweep P pre f)
  have hResidual :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source.1
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) =
        realHilbertProjectionSweep P before x0 -
          realHilbertProjectionSweep P (before ++ [source]) x0 := by
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source.1
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore -
          P source
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore) := by
          rfl
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fbefore hFbefore boundBefore hboundBefore -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta Fafter hFafter boundAfter hboundAfter := by
          rw [← hStep]
      _ =
        realHilbertProjectionSweep P before x0 -
          realHilbertProjectionSweep P (before ++ [source]) x0 := by
          rw [hRepBefore, hRepAfter]
  have hNormSq :=
    congrArg (fun x => ‖x‖ ^ 2) hResidual
  refine
    ⟨Fbefore, hFbefore, boundBefore, hboundBefore,
      Fafter, hFafter, boundAfter, hboundAfter,
      hRepBefore, hRepAfter, ?_, ?_, hne⟩
  · simpa [P, x0] using hResidual
  · simpa [P, x0] using hNormSq

end

end MGAP4D.MathlibAnalytic
