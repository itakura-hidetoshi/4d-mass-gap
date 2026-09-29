import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCondExpOuterRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteOneLinkSweepInvariance
import Mathlib.Tactic

/-!
# Bounded source-invariant representatives of source-fixed joint L2 vectors

A source-fixed L2 class does not make every representative pointwise invariant.
The existing outer-context factorization supplies a measurable representative
that forgets the source coordinate. We cut off that outer-context function,
not an arbitrary ambient representative, using the bound from the bounded
concrete core. This preserves both the L2 class and exact pointwise invariance.

The resulting single representative is suitable for cancelling the direct
observable-change term before estimating target-law response. No conditional
law is identified, no pointwise value of an arbitrary L2 class is used, and
no beta-small leakage coefficient or physical gap is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set

noncomputable section

local instance sourceFixedBoundedRepresentativeIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceFixedBoundedRepresentativeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceFixedBoundedRepresentativeSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceFixedBoundedRepresentativeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceFixedBoundedRepresentativeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceFixedBoundedRepresentativeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- The retained outer context does not see a replacement of the source link. -/
theorem periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap_sourceUpdate
    (H N : ℕ) (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (value : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N source (left, Function.update right source value) =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N source (left, right) := by
  apply Prod.ext
  · rfl
  · funext e
    exact Function.update_of_ne e.property value right

/-- A source-fixed bounded-core vector has one everywhere bounded strongly
measurable representative that is pointwise invariant under source updates.
The bound is imposed on the outer-context function, preserving factorization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_exists_bounded_sourceInvariant_representative
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta)
    (hFixed :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta source f = f) :
    ∃ (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound = f ∧
        ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
          F (left, Function.update right source value) = F (left, right) := by
  classical
  obtain ⟨F0, hF0, bound0, hbound0, hRep0⟩ := hf
  obtain ⟨C, hC, hOuter⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_outerContext_representative
      H N hN beta hbeta source f
  rw [hFixed] at hOuter
  have hConcrete :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta F0 hF0 bound0 hbound0
  rw [hRep0] at hConcrete
  let B : ℝ := max bound0 0
  let outer :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N source
  let S : Set (PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
      H N source) := {a | ‖C a‖ ≤ B}
  let CB := S.indicator C
  let G : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ :=
    fun z => CB (outer z)
  have hB : 0 ≤ B := le_max_right _ _
  have hS : MeasurableSet S := by
    exact measurableSet_le hC.norm.measurable measurable_const
  have hCB : StronglyMeasurable CB := hC.indicator hS
  have hG : StronglyMeasurable G :=
    hCB.comp_measurable
      (measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N source)
  have hCBBound : ∀ a, ‖CB a‖ ≤ B := by
    intro a
    by_cases ha : a ∈ S
    · simpa only [CB, Set.indicator_of_mem ha] using ha
    · simp only [CB, Set.indicator_of_notMem ha, norm_zero]
      exact hB
  have hGBound : ∀ z, ‖G z‖ ≤ B := fun z => hCBBound (outer z)
  have hGae : G =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta] f := by
    filter_upwards [hOuter, hConcrete] with z hzC hzF
    have hzS : outer z ∈ S := by
      change ‖C (outer z)‖ ≤ B
      rw [hzC, hzF]
      exact (hbound0 z).trans (le_max_left _ _)
    change S.indicator C (outer z) = f z
    rw [Set.indicator_of_mem hzS]
    exact hzC
  refine ⟨G, hG, B, hGBound, ?_, ?_⟩
  · apply Lp.ext
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta G hG B hGBound).trans hGae
  · intro left right value
    exact congrArg CB
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap_sourceUpdate
        H N source left right value)

/-- Every genuine source update of a bounded-core vector admits the invariant
representative above. Bounded-core invariance and idempotence are reused. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_sourceInvariant_representative
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta) :
    ∃ (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta source f ∧
        ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
          F (left, Function.update right source value) = F (left, right) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta source
  have hFixed : P (P f) = P f := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg
        (fun T : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta => T f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta source)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_fixed_exists_bounded_sourceInvariant_representative
      H N hN beta hbeta source (P f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_mem_boundedConcreteCore
        H N hN beta hbeta source f hf) hFixed

end

end MGAP4D.MathlibAnalytic
