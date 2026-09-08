import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointRetainedSigmaPairData
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance groundStateJointLeftRetainedSigmaCoordinateBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Repackage the concrete left retained pair data as a function on the
literal left-retained joint-coordinate support. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffColorLink H
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun p i =>
    match i with
    | ⟨Sum.inl e, hi⟩ =>
        p.2 ⟨e, by
          simpa [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet] using hi⟩
    | ⟨Sum.inr e, _⟩ => p.1 e

/-- Recover the concrete left retained pair data from the literal retained
coordinate function. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData
    (H N : ℕ)
    (c : Fin 6) :
    (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c →
      Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun f =>
    (fun e =>
      f (⟨Sum.inr e, by
        simp [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet]⟩ :
        periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c),
    fun e =>
      f (⟨Sum.inl e.1, by
        simpa [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet] using e.2⟩ :
        periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c))

/-- The two left retained presentations are inverse to each other. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate_leftInverse
    (H N : ℕ)
    (c : Fin 6) :
    Function.LeftInverse
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData H N c)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate H N c) := by
  intro p
  apply Prod.ext
  · funext e
    rfl
  · funext e
    change p.2 ⟨e.1, _⟩ = p.2 e
    apply congrArg p.2
    apply Subtype.ext
    rfl

/-- The two left retained presentations are inverse in the other direction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate_rightInverse
    (H N : ℕ)
    (c : Fin 6) :
    Function.RightInverse
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData H N c)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate H N c) := by
  intro f
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e =>
      change f ⟨Sum.inl e, _⟩ = f ⟨Sum.inl e, hi⟩
      apply congrArg f
      apply Subtype.ext
      rfl
  | inr e => rfl

/-- The map from left retained pair data to literal retained coordinates is
measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate
        H N c) := by
  rw [measurable_pi_iff]
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e =>
      exact
        (measurable_pi_apply
          (⟨e, by
            simpa [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet] using hi⟩ :
            PeriodicHypercubicEvenSpatialSliceOffColorLink H
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))).comp
          measurable_snd
  | inr e =>
      exact (measurable_pi_apply e).comp measurable_fst

/-- The inverse map from literal left retained coordinates back to pair data
is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData
        H N c) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      (⟨Sum.inr e, by
        simp [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet]⟩ :
        periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      (⟨Sum.inl e.1, by
        simpa [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet] using e.2⟩ :
        periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)

/-- The old pair-data presentation and the literal left-retained coordinate
presentation are measurably equivalent. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataCoordinateMeasurableEquiv
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffColorLink H
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c →
        Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toEquiv :=
    { toFun :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate H N c
      invFun :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData H N c
      left_inv :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate_leftInverse
          H N c
      right_inv :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate_rightInverse
          H N c }
  measurable_toFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataToCoordinate
      H N c
  measurable_invFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateToPairData
      H N c

/-- The literal left retained-coordinate restriction is the measurable
repackaging of the previously used retained pair data. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction_eq_pairDataCoordinate_comp
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
        H N c =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataCoordinateMeasurableEquiv
        H N c ∘
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData H N c := by
  funext z i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e => rfl
  | inr e => rfl

/-- Hence the actual left-color retained sigma-algebra is exactly the
sigma-algebra generated by the literal retained coordinate restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_eq_comap_leftRetainedCoordinateRestriction
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
          H N c)
        inferInstance := by
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_eq_comap_leftRetainedPairData]
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction_eq_pairDataCoordinate_comp]
  rw [← MeasurableSpace.comap_comp]
  rw [(periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairDataCoordinateMeasurableEquiv
    H N c).measurableEmbedding.comap_eq]

end

end MathlibAnalytic
end MGAP4D
