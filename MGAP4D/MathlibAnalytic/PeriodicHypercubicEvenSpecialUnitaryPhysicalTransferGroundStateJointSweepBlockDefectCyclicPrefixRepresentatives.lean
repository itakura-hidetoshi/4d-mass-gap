import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteOneLinkSweepInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSecondVisitRepresentative
import Mathlib.Tactic

/-!
# Bounded representatives along every cyclic between-visits prefix

PR #4894 identifies the exact between-visits order for a target link as

  suffix ++ pre.

PR #4895 constructs a bounded representative after the whole cyclic list.
For source-update semantics one also needs the intermediate states before and
after each individual cyclic source update.

The bounded concrete core is already invariant under every finite same-color
one-link sweep.  Therefore, starting from the first target projection, every

  (suffix ++ pre).take k

prefix state remains in the bounded concrete core.  This file records that
fact and chooses bounded strongly measurable concrete representatives
simultaneously for every prefix length k.

No quotient representative is evaluated pointwise.  The representatives are
obtained only by eliminating membership in the established bounded concrete
core.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance cyclicPrefixRepresentativesSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance cyclicPrefixRepresentativesSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance cyclicPrefixRepresentativesSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance cyclicPrefixRepresentativesSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance cyclicPrefixRepresentativesSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance cyclicPrefixRepresentativesSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every prefix of the cyclic between-visits sweep, starting immediately
after the first target projection, remains in the bounded concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicPrefix_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (k : ℕ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        ((suffix ++ pre).take k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            pre f)) ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  have hPre :
      realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          pre f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
      H N hN beta hbeta color pre f hf
  have hTarget :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            pre f) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2_mem_boundedConcreteCore
      H N hN beta hbeta color target
      (realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        pre f)
      hPre
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
      H N hN beta hbeta color ((suffix ++ pre).take k)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color target
        (realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          pre f))
      hTarget

/-- Every cyclic prefix state has a bounded strongly measurable concrete
representative in the genuine joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicPrefix_exists_boundedRepresentative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (k : ℕ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          ((suffix ++ pre).take k)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target
            (realHilbertProjectionSweep
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color)
              pre f)) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicPrefix_mem_boundedConcreteCore
      H N hN beta hbeta color pre suffix target k f hf

/-- Choose bounded concrete representatives simultaneously for every prefix
length of the cyclic between-visits trajectory. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicPrefix_boundedRepresentatives
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (F :
        ℕ →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ k, StronglyMeasurable (F k))
      (bound : ℕ → ℝ)
      (hbound : ∀ k z, ‖F k z‖ ≤ bound k),
      ∀ k,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta (F k) (hF k) (bound k) (hbound k) =
          realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            ((suffix ++ pre).take k)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color target
              (realHilbertProjectionSweep
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                  H N hN beta hbeta color)
                pre f)) := by
  have hWitness :
      ∀ k : ℕ,
        ∃
          (F :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
          (hF : StronglyMeasurable F)
          (bound : ℝ)
          (hbound : ∀ z, ‖F z‖ ≤ bound),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound =
            realHilbertProjectionSweep
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color)
              ((suffix ++ pre).take k)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color target
                (realHilbertProjectionSweep
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                    H N hN beta hbeta color)
                  pre f)) := by
    intro k
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicPrefix_exists_boundedRepresentative
        H N hN beta hbeta color pre suffix target k f hf
  choose F hF bound hbound hRep using hWitness
  exact ⟨F, hF, bound, hbound, hRep⟩

end

end MGAP4D.MathlibAnalytic
