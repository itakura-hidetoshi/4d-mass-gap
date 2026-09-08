import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointRetainedSigmaPairData
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance groundStateJointRightRetainedSigmaCoordinateBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Repackage the concrete right retained pair data as a function on the
literal right-retained joint-coordinate support. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffColorLink H
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun p i =>
    match i.1 with
    | Sum.inl e => p.1 e
    | Sum.inr e =>
        p.2 ⟨e, by
          simpa [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using i.2⟩

/-- Recover the concrete right retained pair data from the literal retained
coordinate function. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData
    (H N : ℕ)
    (c : Fin 6) :
    (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c →
      Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun f =>
    (fun e =>
      f ⟨Sum.inl e, by
        simp [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet]⟩,
    fun e =>
      f ⟨Sum.inr e.1, by
        simpa [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using e.2⟩)

/-- The two right retained presentations are inverse to each other. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate_leftInverse
    (H N : ℕ)
    (c : Fin 6) :
    Function.LeftInverse
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData H N c)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate H N c) := by
  intro p
  apply Prod.ext
  · funext e
    rfl
  · funext e
    change p.2 ⟨e.1, _⟩ = p.2 e
    congr

/-- The two right retained presentations are inverse in the other direction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate_rightInverse
    (H N : ℕ)
    (c : Fin 6) :
    Function.RightInverse
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData H N c)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate H N c) := by
  intro f
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e => rfl
  | inr e =>
      change f ⟨Sum.inr e, _⟩ = f ⟨Sum.inr e, hi⟩
      congr

/-- The map from right retained pair data to literal retained coordinates is
measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate
        H N c) := by
  rw [measurable_pi_iff]
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e =>
      exact (measurable_pi_apply e).comp measurable_fst
  | inr e =>
      exact
        (measurable_pi_apply
          ⟨e, by
            simpa [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using hi⟩).comp
          measurable_snd

/-- The inverse map from literal right retained coordinates back to pair data
is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData
        H N c) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      ⟨Sum.inl e, by
        simp [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet]⟩
  · rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply
      ⟨Sum.inr e.1, by
        simpa [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet] using e.2⟩

/-- The old pair-data presentation and the literal retained-coordinate
presentation are measurably equivalent. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataCoordinateMeasurableEquiv
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffColorLink H
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c →
        Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toEquiv :=
    { toFun :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate H N c
      invFun :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData H N c
      left_inv :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate_leftInverse
          H N c
      right_inv :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate_rightInverse
          H N c }
  measurable_toFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataToCoordinate
      H N c
  measurable_invFun :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateToPairData
      H N c

/-- The literal right retained-coordinate restriction is the measurable
repackaging of the previously used retained pair data. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_pairDataCoordinate_comp
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
        H N c =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataCoordinateMeasurableEquiv
        H N c ∘
      periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData H N c := by
  funext z i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl e => rfl
  | inr e => rfl

/-- Hence the actual right-color retained sigma-algebra is exactly the
sigma-algebra generated by the literal retained coordinate restriction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
          H N c)
        inferInstance := by
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedPairData]
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_eq_pairDataCoordinate_comp]
  rw [← MeasurableSpace.comap_comp]
  rw [(periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairDataCoordinateMeasurableEquiv
    H N c).measurableEmbedding.comap_eq]

end

end MathlibAnalytic
end MGAP4D
