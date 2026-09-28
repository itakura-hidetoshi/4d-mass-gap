import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointRightRetainedSigmaCoordinateBridge
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

/-!
# One-link retained coordinate bridge

This unit gives the genuine one-link retained sigma-algebra the same literal
joint-coordinate presentation already available for the six spatial-color
blocks.  It also proves the finite combinatorial identity needed downstream:
intersecting all one-link retained supports inside one fixed spatial color
leaves exactly that color's retained support.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance oneLinkRetainedCoordinateBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneLinkRetainedCoordinateBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Joint coordinates retained when one right-boundary spatial link is updated:
all left coordinates and every right coordinate except the target. -/
def periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Set (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  {i | match i with
    | Sum.inl _ => True
    | Sum.inr e => e ≠ target}

/-- The data retained by one right-boundary link update, in the older pair
presentation: complete left boundary plus off-target right boundary. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairData
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun z =>
    (z.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)

/-- The one-link retained pair-data map is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairData
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairData
        H N target) := by
  exact measurable_fst.prodMk
    ((measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction
      H N target).comp measurable_snd)

/-- The existing one-link retained sigma-algebra is exactly the pullback of
the single retained pair-data map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedPairData
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairData
          H N target)
        inferInstance := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairData
  symm
  exact MeasurableSpace.comap_prodMk _ _

/-- Repackage one-link retained pair data as a function on the literal retained
joint-coordinate support. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataToCoordinate
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun p i =>
    match i with
    | ⟨Sum.inl e, _⟩ => p.1 e
    | ⟨Sum.inr e, hi⟩ =>
        p.2 ⟨e, by
          simpa [periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet]
            using hi⟩

/-- Recover one-link retained pair data from the literal retained-coordinate
function. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateToPairData
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun f =>
    (fun e =>
      f ⟨Sum.inl e, by
        simp [periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet]⟩,
    fun e =>
      f ⟨Sum.inr e.1, by
        simpa [periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet]
          using e.2⟩)

/-- Pair-data to retained-coordinate conversion is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataToCoordinate
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataToCoordinate
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
            simpa [periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet]
              using hi⟩ :
            PeriodicHypercubicEvenSpatialSliceOffTargetLink H target)).comp
          measurable_snd

/-- Retained-coordinate to pair-data conversion is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateToPairData
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateToPairData
        H N target) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      (⟨Sum.inl e, by
        simp [periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet]⟩ :
        periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet H target)
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      (⟨Sum.inr e.1, by
        simpa [periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet]
          using e.2⟩ :
        periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet H target)

/-- The two one-link retained presentations are measurably equivalent. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataCoordinateMeasurableEquiv
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataToCoordinate
      H N target
  invFun :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateToPairData
      H N target
  left_inv := by
    intro p
    apply Prod.ext
    · funext e
      rfl
    · funext e
      change p.2 ⟨e.1, _⟩ = p.2 e
      apply congrArg p.2
      apply Subtype.ext
      rfl
  right_inv := by
    intro f
    funext i
    rcases i with ⟨i, hi⟩
    cases i with
    | inl e =>
        rfl
    | inr e =>
        change f ⟨Sum.inr e, _⟩ = f ⟨Sum.inr e, hi⟩
        apply congrArg f
        apply Subtype.ext
        rfl
  measurable_toFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataToCoordinate
      H N target
  measurable_invFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateToPairData
      H N target

/-- Literal restriction of the unified joint-coordinate presentation to the
one-link retained support. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun z i =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N z i.1

/-- The literal one-link retained-coordinate restriction is the measurable
repackaging of the retained pair data. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_pairDataCoordinate_comp
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction
        H N target =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataCoordinateMeasurableEquiv
        H N target ∘
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairData
        H N target := by
  funext z i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e =>
      rfl
  | inr e =>
      rfl

/-- Hence the genuine one-link retained sigma-algebra is exactly the pullback
of the literal retained-coordinate restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedCoordinateRestriction
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction
          H N target)
        inferInstance := by
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_retainedPairData]
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_pairDataCoordinate_comp]
  rw [← MeasurableSpace.comap_comp]
  rw [(periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedPairDataCoordinateMeasurableEquiv
    H N target).measurableEmbedding.comap_eq]

/-- The literal one-link retained restriction is exactly a predicate-selected
restriction of the unified joint-coordinate presentation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction_eq_piRestriction_comp
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkRetainedCoordinateRestriction
        H N target =
      (pairHaarPiRestriction (K := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (fun i => i ∈
          periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
            H target)) ∘
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N := by
  rfl

/-- Intersecting the retained supports of every one-link update in one fixed
spatial color leaves exactly the right-color retained support. -/
theorem
    periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet_fixedColor_iInter
    (H : ℕ) (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    (fun i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
      ∀ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
        i ∈ periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
          H e.1) =
    (fun i => i ∈
      periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
        H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)) := by
  funext i
  apply propext
  cases i with
  | inl e =>
      simp [
        periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet,
        periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet]
  | inr r =>
      constructor
      · intro hall
        have hne : periodicHypercubicEvenSpatialSliceLinkColor H r ≠ color := by
          intro hcolor
          let er :
              PeriodicHypercubicEvenFixedSpatialColorLink H color :=
            ⟨r, hcolor⟩
          have hr := hall er
          simpa [
            er,
            periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet] using hr
        simpa [
          periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using hne
      · intro hret e
        have hcolor :
            periodicHypercubicEvenSpatialSliceLinkColor H r ≠ color := by
          simpa [
            periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using hret
        change r ≠ e.1
        intro hre
        apply hcolor
        rw [hre]
        exact e.2

/-- List form matching the canonical complete same-color one-link sweep. -/
theorem
    periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet_fixedColor_univList
    (H : ℕ) (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    (fun i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
      ∀ e ∈ ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList),
        i ∈ periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet
          H e.1) =
    (fun i => i ∈
      periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
        H (periodicHypercubicEvenGroundStateSpatialColorEquivFin color)) := by
  rw [
    ← periodicHypercubicEvenGroundStateJointSpatialLinkRetainedCoordinateSet_fixedColor_iInter
      H color]
  funext i
  apply propext
  simp

end

end MGAP4D.MathlibAnalytic
