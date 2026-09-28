import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSpatialCoordinateMeasurableEquiv
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Tactic

/-!
# Literal joint-coordinate support for one-link retained sigma algebras

The ground-state one-link conditional expectation retains the complete left
boundary and every right-boundary spatial link except one selected target.

This file repackages that existing retained data as a literal restriction of
the unified left/right spatial-coordinate presentation.  Consequently

  SpatialLinkMeasurableSpace(target)
    = comap (oneLinkRetainedRestriction target) inferInstance.

For one fixed six-spatial color we also prove the exact support identity

  intersection_{target of this color} oneLinkRetainedSupport(target)
    = colorRetainedSupport.

This is pure finite-coordinate geometry.  No probability law, conditional
expectation comparison, independence assumption, cardinality estimate, or
analytic coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set

noncomputable section

local instance groundStateOneLinkRetainedCoordinateBridgeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateOneLinkRetainedCoordinateBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal unified-coordinate support retained by one right-boundary
one-link update: every left coordinate and every right coordinate except the
selected target. -/
def periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Set (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  {i | match i with
    | Sum.inl _ => True
    | Sum.inr e => e ≠ target}

/-- The existing concrete retained pair data for one right-boundary one-link
update: the complete left boundary together with the off-target right
boundary. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairData
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun z =>
    (z.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)

/-- The one-link retained pair-data map is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairData
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairData
        H N target) := by
  exact measurable_fst.prodMk
    ((measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction
      H N target).comp measurable_snd)

/-- The existing one-link retained sigma algebra is exactly the pullback of
the single retained pair-data map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_rightOneLinkRetainedPairData
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairData
          H N target)
        inferInstance := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairData
  symm
  exact MeasurableSpace.comap_prodMk _ _

/-- Repackage one-link retained pair data as a function on the literal retained
joint-coordinate support. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun p i =>
    match i with
    | ⟨Sum.inl e, _⟩ => p.1 e
    | ⟨Sum.inr e, hi⟩ =>
        p.2 ⟨e, by
          simpa [
            periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet] using hi⟩

/-- Recover one-link retained pair data from the literal retained-coordinate
function. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun f =>
    (fun e =>
      f ⟨Sum.inl e, by
        simp [
          periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet]⟩,
    fun e =>
      f ⟨Sum.inr e.1, by
        simpa [
          periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet] using e.2⟩)

/-- The literal one-link retained coordinate presentations are inverse. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate_leftInverse
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Function.LeftInverse
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
        H N target)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
        H N target) := by
  intro p
  apply Prod.ext
  · funext e
    rfl
  · funext e
    change p.2 ⟨e.1, _⟩ = p.2 e
    apply congrArg p.2
    apply Subtype.ext
    rfl

/-- Inverse identity in the other direction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate_rightInverse
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Function.RightInverse
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
        H N target)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
        H N target) := by
  intro f
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e => rfl
  | inr e =>
      change f ⟨Sum.inr e, _⟩ = f ⟨Sum.inr e, hi⟩
      apply congrArg f
      apply Subtype.ext
      rfl

/-- Pair-data to literal retained-coordinate repackaging is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
        H N target) := by
  rw [measurable_pi_iff]
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e =>
      exact (measurable_pi_apply e).comp measurable_fst
  | inr e =>
      exact
        (measurable_pi_apply
          (⟨e, by
            simpa [
              periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet] using hi⟩ :
            PeriodicHypercubicEvenSpatialSliceOffTargetLink H target)).comp
          measurable_snd

/-- Literal retained-coordinate to pair-data repackaging is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
        H N target) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      (⟨Sum.inl e, by
        simp [
          periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet]⟩ :
        periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet H target)
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      (⟨Sum.inr e.1, by
        simpa [
          periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet] using e.2⟩ :
        periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet H target)

/-- Measurable equivalence between the existing one-link retained pair data
and the literal retained joint coordinates. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataCoordinateMeasurableEquiv
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toEquiv :=
    { toFun :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
          H N target
      invFun :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
          H N target
      left_inv :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate_leftInverse
          H N target
      right_inv :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate_rightInverse
          H N target }
  measurable_toFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataToCoordinate
      H N target
  measurable_invFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateToPairData
      H N target

/-- Literal one-link retained-coordinate restriction on the original pair
configuration carrier. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun z i =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N z i.1

/-- The literal one-link retained-coordinate restriction is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction
        H N target) := by
  rw [measurable_pi_iff]
  intro i
  exact
    (measurable_pi_apply i.1).comp
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N).measurable

/-- The literal restriction is exactly the measurable repackaging of the
existing retained pair data. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction_eq_pairDataCoordinate_comp
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction
        H N target =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataCoordinateMeasurableEquiv
        H N target ∘
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairData
        H N target := by
  funext z i
  rcases i with ⟨i, hi⟩
  cases i <;> rfl

/-- Hence the actual one-link retained sigma algebra is exactly the pullback
of the literal retained-coordinate restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_rightOneLinkRetainedCoordinateRestriction
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction
          H N target)
        inferInstance := by
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_rightOneLinkRetainedPairData,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction_eq_pairDataCoordinate_comp,
    ← MeasurableSpace.comap_comp]
  rw [
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedPairDataCoordinateMeasurableEquiv
      H N target).measurableEmbedding.comap_eq]

/-- The literal one-link retained restriction is exactly the generic finite
product coordinate restriction after the unified coordinate equivalence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction_eq_piRestriction_comp
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightOneLinkRetainedCoordinateRestriction
        H N target =
      (pairHaarPiRestriction
        (K := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (fun i =>
          i ∈ periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet
            H target)) ∘
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N := by
  rfl

/-- Intersecting the literal one-link retained supports over every link of one
fixed color leaves exactly the corresponding color-retained support. -/
theorem
    periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet_iInter_fixedColor_eq_rightRetainedColor
    (H : ℕ)
    (c : Fin 6) :
    (fun i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
      ∀ target :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c),
        i ∈ periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet
          H target.1) =
      (fun i =>
        i ∈ periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c) := by
  funext i
  apply propext
  constructor
  · intro hi
    cases i with
    | inl e =>
        simp [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet]
    | inr e =>
        have hneColor :
            periodicHypercubicEvenSpatialSliceLinkColor H e ≠
              periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c := by
          intro heq
          let target :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) :=
            ⟨e, heq⟩
          have hret := hi target
          simpa [
            periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet,
            target] using hret
        simpa [
          periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using
          hneColor
  · intro hi target
    cases i with
    | inl e =>
        simp [
          periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet]
    | inr e =>
        have hneColor :
            periodicHypercubicEvenSpatialSliceLinkColor H e ≠
              periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c := by
          simpa [
            periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using hi
        have hne : e ≠ target.1 := by
          intro heq
          apply hneColor
          rw [heq]
          exact target.2
        simpa [
          periodicHypercubicEvenGroundStateJointRightOneLinkRetainedCoordinateSet] using
          hne

end

end MGAP4D.MathlibAnalytic
