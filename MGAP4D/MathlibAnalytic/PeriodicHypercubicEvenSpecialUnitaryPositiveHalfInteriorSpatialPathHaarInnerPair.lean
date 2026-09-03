import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarBoundaryInterior
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfInnerPairHaarIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfInnerPairHaarCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfInnerPairHaarSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfInnerPairHaarMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfInnerPairHaarBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfInnerPairHaarSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

/-- After the two strict-interior endpoint slices have been separated, the
remaining deeper interior of a positive half-cylinder with `H = M + 2` is a
single `Fin M`-indexed path. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath
    (M N : ℕ) : Type :=
  Fin M → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N

/-- Product one-slice Haar law on the deeper interior slices. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure
    (M N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) :=
  Measure.pi
    (fun _ : Fin M =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (M + 2) N)

instance
    periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaar_isProbabilityMeasure
    (M N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure
  infer_instance

/-- Haar law after splitting the strict interior of an `H = M + 2` half-cylinder
into the ordered inner boundary pair and the remaining deeper interior. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure
    (M N : ℕ) :
    Measure
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N).prod
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)

instance
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaar_isProbabilityMeasure
    (M N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure
        M N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure
  infer_instance

/-- For a nondegenerate half-cylinder written canonically as `H = M + 2`, split
the strict interior path `(A₁, ..., A_H)` into its ordered endpoint pair
`(A₁, A_H)` and the deeper path `(A₂, ..., A_{H-1})`.

The already-canonical `Fin (M+2) ≃ Fin 2 ⊕ Fin M` time equivalence is reused,
so no proof-dependent cast of a hypothesis `2 ≤ H` enters the coordinates. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
    (M N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath (M + 2) N ≃ᵐ
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) :=
  let X : Fin 2 ⊕ Fin M → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv M
  let reindex := MeasurableEquiv.piCongrLeft X e
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N)
  let deep :=
    MeasurableEquiv.refl
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N)
  reindex.trans (split.trans (MeasurableEquiv.prodCongr pair deep))

/-- The first component of the strict-interior split is the first inward slice
`A₁`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_fst_fst
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N path).1.1 = path 0 := by
  rfl

/-- The second component of the strict-interior endpoint pair is the last
inward slice `A_H`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_fst_snd
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath (M + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N path).1.2 = path (Fin.last (M + 1)) := by
  change
    path
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv M).symm
          (Sum.inl (1 : Fin 2))) =
      path (Fin.last (M + 1))
  apply congrArg path
  apply Fin.ext
  simp [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- The deeper-interior coordinate `k` is exactly the next strict-interior
slice, namely `A_{k+2}` in the original complete path. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_snd_apply
    (M N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath (M + 2) N)
    (k : Fin M) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N path).2 k =
      path ⟨k.1 + 1, by omega⟩ := by
  change
    path
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv M).symm
          (Sum.inr k)) =
      path ⟨k.1 + 1, by omega⟩
  apply congrArg path
  apply Fin.ext
  rfl

/-- Exact finite-product Haar independence of the two distinct inward endpoint
slices for `H = M + 2`: strict-interior Haar is transported to inner pair-Haar
times deeper-interior Haar.

This theorem deliberately starts at `H = 2`.  The `H = 1` geometry has only one
central slice and therefore belongs to the separate diagonal pushforward case,
not to an independent pair-Haar law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_measurePreserving
    (M N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
        M N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
        (M + 2) N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure
        M N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (M + 2) N
  let X : Fin 2 ⊕ Fin M → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv M
  let reindex := MeasurableEquiv.piCongrLeft X e
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N)
  let deep :=
    MeasurableEquiv.refl
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N)
  let nested := MeasurableEquiv.prodCongr pair deep

  have hReindex :
      MeasurePreserving reindex
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
          (M + 2) N)
        (Measure.pi (fun _ : Fin 2 ⊕ Fin M => μ)) := by
    simpa [reindex, e, X,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure,
      periodicHypercubicEvenPositiveHalfCylinderSlabCount] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Fin 2 ⊕ Fin M => μ) e)

  have hSplit :
      MeasurePreserving split
        (Measure.pi (fun _ : Fin 2 ⊕ Fin M => μ))
        ((Measure.pi (fun _ : Fin 2 => μ)).prod
          (Measure.pi (fun _ : Fin M => μ))) := by
    simpa [split, X] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : Fin 2 ⊕ Fin M => μ))

  have hPair :
      MeasurePreserving pair
        (Measure.pi (fun _ : Fin 2 => μ))
        (μ.prod μ) := by
    simpa [pair] using
      (MeasureTheory.measurePreserving_piFinTwo
        (fun _ : Fin 2 => μ))

  have hDeep :
      MeasurePreserving deep
        (Measure.pi (fun _ : Fin M => μ))
        (Measure.pi (fun _ : Fin M => μ)) := by
    simpa [deep] using
      (MeasurePreserving.id (Measure.pi (fun _ : Fin M => μ)))

  have hNested :
      MeasurePreserving nested
        ((Measure.pi (fun _ : Fin 2 => μ)).prod
          (Measure.pi (fun _ : Fin M => μ)))
        ((μ.prod μ).prod (Measure.pi (fun _ : Fin M => μ))) := by
    simpa [nested] using hPair.prod hDeep

  have hAll := (hReindex.trans hSplit).trans hNested
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount,
    reindex, split, pair, deep, nested, X, e, μ] using hAll

end

end MathlibAnalytic
end MGAP4D
