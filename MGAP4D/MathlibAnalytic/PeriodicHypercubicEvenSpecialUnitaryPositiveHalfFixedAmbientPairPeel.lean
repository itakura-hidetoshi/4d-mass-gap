import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarInnerPair
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientPairPeelIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientPairPeelCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientPairPeelSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientPairPeelMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientPairPeelBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientPairPeelSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A finite inward spatial chain whose length `R` is independent of the
ambient spatial extent `H`.

This separation is essential for transfer recursion: peeling one temporal
layer must shorten only the remaining chain, not change the spatial-slice
configuration type. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
    (H R N : ℕ) : Type :=
  Fin R → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N

/-- Product Haar law on a fixed-ambient inward chain. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
    (H R N : ℕ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N) :=
  Measure.pi
    (fun _ : Fin R =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

instance
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaar_isProbabilityMeasure
    (H R N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
        H R N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
  infer_instance

/-- Haar law after peeling the two endpoints of a fixed-ambient chain of
length `R+2`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
    (H R N : ℕ) :
    Measure
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
      H R N)

instance
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaar_isProbabilityMeasure
    (H R N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
        H R N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
  infer_instance

/-- Canonically peel the two endpoints from a chain of length `R+2` while
keeping the ambient spatial extent `H` fixed.

The output is the ordered endpoint pair together with the remaining `Fin R`
chain.  This is the coordinate seam needed before any recursive transfer
operator statement can be made without changing Hilbert spaces. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
    (H R N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
        H (R + 2) N ≃ᵐ
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N) :=
  let X : Fin 2 ⊕ Fin R → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv R
  let reindex := MeasurableEquiv.piCongrLeft X e
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  let deep :=
    MeasurableEquiv.refl
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N)
  reindex.trans (split.trans (MeasurableEquiv.prodCongr pair deep))

/-- The first peeled coordinate is the first slice of the fixed-ambient
chain. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv_fst_fst
    (H R N : ℕ)
    (path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
        H (R + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
      H R N path).1.1 = path 0 := by
  rfl

/-- The second peeled coordinate is the last slice of the fixed-ambient
chain. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv_fst_snd
    (H R N : ℕ)
    (path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
        H (R + 2) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
      H R N path).1.2 = path (Fin.last (R + 1)) := by
  let X : Fin 2 ⊕ Fin R → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv R
  let reindex := MeasurableEquiv.piCongrLeft X e
  let j : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount R + 1) :=
    Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount R)
  change reindex path (Sum.inl (1 : Fin 2)) = path (Fin.last (R + 1))
  have hEval : reindex path (e j) = path j := by
    simpa [reindex] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := X) e path j)
  have hj : e j = Sum.inl (1 : Fin 2) := by
    simpa [e, j] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_antipodal
        R)
  rw [hj] at hEval
  simpa [j, periodicHypercubicEvenPositiveHalfCylinderSlabCount] using hEval

/-- Deep coordinate `k` is exactly the original chain coordinate `k+1`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv_snd_apply
    (H R N : ℕ)
    (path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
        H (R + 2) N)
    (k : Fin R) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
      H R N path).2 k = path ⟨k.1 + 1, by omega⟩ := by
  let X : Fin 2 ⊕ Fin R → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv R
  let reindex := MeasurableEquiv.piCongrLeft X e
  let j : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount R + 1) :=
    ⟨k.1 + 1, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  change reindex path (Sum.inr k) = path ⟨k.1 + 1, by omega⟩
  have hEval : reindex path (e j) = path j := by
    simpa [reindex] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := X) e path j)
  have hj : e j = Sum.inr k := by
    simpa [e, j] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_interior
        R k)
  rw [hj] at hEval
  simpa [j, periodicHypercubicEvenPositiveHalfCylinderSlabCount] using hEval

/-- Exact finite-product Haar preservation of fixed-ambient endpoint peeling.
Only the remaining-chain length changes; the spatial slice carrier and its Haar
law stay fixed at ambient extent `H`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv_measurePreserving
    (H R N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
        H R N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
        H (R + 2) N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
        H R N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let X : Fin 2 ⊕ Fin R → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv R
  let reindex := MeasurableEquiv.piCongrLeft X e
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  let deep :=
    MeasurableEquiv.refl
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N)
  let nested := MeasurableEquiv.prodCongr pair deep

  have hReindex :
      MeasurePreserving reindex
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
          H (R + 2) N)
        (Measure.pi (fun _ : Fin 2 ⊕ Fin R => μ)) := by
    simpa [reindex, e, X,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure,
      periodicHypercubicEvenPositiveHalfCylinderSlabCount] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Fin 2 ⊕ Fin R => μ) e)

  have hSplit :
      MeasurePreserving split
        (Measure.pi (fun _ : Fin 2 ⊕ Fin R => μ))
        ((Measure.pi (fun _ : Fin 2 => μ)).prod
          (Measure.pi (fun _ : Fin R => μ))) := by
    simpa [split, X] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : Fin 2 ⊕ Fin R => μ))

  have hPair :
      MeasurePreserving pair
        (Measure.pi (fun _ : Fin 2 => μ))
        (μ.prod μ) := by
    simpa [pair] using
      (MeasureTheory.measurePreserving_piFinTwo
        (fun _ : Fin 2 => μ))

  have hDeep :
      MeasurePreserving deep
        (Measure.pi (fun _ : Fin R => μ))
        (Measure.pi (fun _ : Fin R => μ)) := by
    simpa [deep] using
      (MeasurePreserving.id (Measure.pi (fun _ : Fin R => μ)))

  have hNested :
      MeasurePreserving nested
        ((Measure.pi (fun _ : Fin 2 => μ)).prod
          (Measure.pi (fun _ : Fin R => μ)))
        ((μ.prod μ).prod (Measure.pi (fun _ : Fin R => μ))) := by
    simpa [nested] using hPair.prod hDeep

  have hAll := (hReindex.trans hSplit).trans hNested
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount,
    reindex, split, pair, deep, nested, X, e, μ] using hAll

end

end MathlibAnalytic
end MGAP4D
