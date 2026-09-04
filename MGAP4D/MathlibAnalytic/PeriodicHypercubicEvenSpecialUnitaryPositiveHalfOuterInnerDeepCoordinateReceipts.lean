import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarOuterInnerDeep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderBoundaryPairFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfOuterInnerDeepCoordinatesIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfOuterInnerDeepCoordinatesCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfOuterInnerDeepCoordinatesSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfOuterInnerDeepCoordinatesMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfOuterInnerDeepCoordinatesBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfOuterInnerDeepCoordinatesSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_outer_fst
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N path).1.1 =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path).1 := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_outer_snd
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N path).1.2 =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path).2 := by
  let X : Fin 2 ⊕ Fin (M + 2) → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv (M + 2)
  let reindex := MeasurableEquiv.piCongrLeft X e
  change reindex path (Sum.inl (1 : Fin 2)) =
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path).2
  have hEval :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := X) e path
      (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount (M + 2)))
  have hj :
      e (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount (M + 2))) =
        Sum.inl (1 : Fin 2) := by
    exact
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_antipodal
        (M + 2)
  rw [hj] at hEval
  rw [hEval]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex
  apply congrArg path
  apply Fin.ext
  simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_zero
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N path).2 0 =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path).1 := by
  let X : Fin 2 ⊕ Fin (M + 2) → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv (M + 2)
  let reindex := MeasurableEquiv.piCongrLeft X e
  let k : Fin (M + 2) := 0
  let j : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (M + 2) + 1) :=
    ⟨k.1 + 1, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  change reindex path (Sum.inr (0 : Fin (M + 2))) =
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path).1
  have hEval :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := X) e path j
  have hj : e j = Sum.inr k := by
    simpa [j, k] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_interior
        (M + 2) k)
  rw [hj] at hEval
  simpa [k] only using hEval.trans (by
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex
    apply congrArg path
    apply Fin.ext
    simp [j])

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_last
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N path).2 (Fin.last (M + 1)) =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path).2 := by
  let X : Fin 2 ⊕ Fin (M + 2) → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv (M + 2)
  let reindex := MeasurableEquiv.piCongrLeft X e
  let k : Fin (M + 2) := Fin.last (M + 1)
  let j : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (M + 2) + 1) :=
    ⟨k.1 + 1, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  change reindex path (Sum.inr (Fin.last (M + 1))) =
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path).2
  have hEval :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := X) e path j
  have hj : e j = Sum.inr k := by
    simpa [j, k] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_interior
        (M + 2) k)
  rw [hj] at hEval
  have hk : k = Fin.last (M + 1) := by rfl
  rw [hk] at hEval
  rw [hEval]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex
  apply congrArg path
  apply Fin.ext
  simp [j, k, periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- The first pair in the three-factor Haar coordinates is exactly the actual
ordered outer reflection-boundary pair used by the path Markov factorization. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv_outerPair
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
      M N path).1 =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path := by
  change
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N path).1 =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path
  apply Prod.ext
  · exact
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_outer_fst
        M N path
  · exact
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_outer_snd
        M N path

/-- The second exposed pair in the three-factor Haar coordinates is exactly the
actual ordered inward pair used by the one-step pair kernel. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv_innerPair
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
      M N path).2.1 =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path := by
  let interior :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N path).2
  change
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N interior).1 =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path
  apply Prod.ext
  · calc
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
          M N interior).1.1 = interior 0 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_fst_fst
            M N interior
      _ = (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path).1 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_zero
            M N path
  · calc
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
          M N interior).1.2 = interior (Fin.last (M + 1)) := by
        exact
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_fst_snd
            M N interior
      _ = (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path).2 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_last
            M N path

end

end MathlibAnalytic
end MGAP4D
