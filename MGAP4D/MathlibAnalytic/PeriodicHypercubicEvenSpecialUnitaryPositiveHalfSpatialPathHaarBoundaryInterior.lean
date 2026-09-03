import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderBoundaryPairFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfSpatialPathBoundaryInteriorIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfSpatialPathBoundaryInteriorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfSpatialPathBoundaryInteriorSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfSpatialPathBoundaryInteriorMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfSpatialPathBoundaryInteriorBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfSpatialPathBoundaryInteriorSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The strict interior spatial path consists of the slices at Euclidean times
`1, ..., H`.  It is deliberately a single `Fin H`-indexed path.  Thus for
`H = 1` there is one central Haar variable, not two artificially independent
copies of the same geometric slice. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath
    (H N : ℕ) : Type :=
  Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N

/-- Product one-slice Haar law on all strict interior spatial slices. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N) :=
  Measure.pi
    (fun _ : Fin H =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
  infer_instance

/-- The target Haar law after separating the two outer reflection boundaries
from all strict interior spatial slices. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure
    (H N : ℕ) :
    Measure
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure
  infer_instance

/-- Exact time-index classification of the actual complete positive-half path
carrier.  The two distinguished `Fin 2` coordinates are ordered primary then
antipodal; `Fin H` carries the strict interior times `1, ..., H`. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv
    (H : ℕ) :
    Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) ≃
      (Fin 2 ⊕ Fin H) where
  toFun j :=
    if h0 : j.1 = 0 then
      Sum.inl 0
    else if hlast : j.1 = H + 1 then
      Sum.inl 1
    else
      Sum.inr ⟨j.1 - 1, by
        have hjlt : j.1 < H + 2 := by
          simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using j.2
        omega⟩
  invFun z :=
    match z with
    | Sum.inl i =>
        if hi : i.1 = 0 then
          0
        else
          ⟨H + 1, by
            simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
    | Sum.inr k => ⟨k.1 + 1, by
        simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  left_inv j := by
    by_cases h0 : j.1 = 0
    · apply Fin.ext
      simp [h0]
    · by_cases hlast : j.1 = H + 1
      · apply Fin.ext
        simp [hlast]
      · have hjpos : 1 ≤ j.1 := Nat.one_le_iff_ne_zero.mpr h0
        apply Fin.ext
        simp [h0, hlast, Nat.sub_add_cancel hjpos]
  right_inv z := by
    rcases z with i | k
    · fin_cases i <;> simp
    · have hk : k.1 ≠ H := ne_of_lt k.2
      simp [hk]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_primary
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H 0 =
      Sum.inl 0 := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_antipodal
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H
        (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) =
      Sum.inl 1 := by
  have hslab :
      periodicHypercubicEvenPositiveHalfCylinderSlabCount H = H + 1 := by
    rfl
  rw [hslab]
  simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_interior
    (H : ℕ)
    (k : Fin H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H
        ⟨k.1 + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩ =
      Sum.inr k := by
  have hk : k.1 ≠ H := ne_of_lt k.2
  simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv, hk]

/-- Measurable equivalence separating a complete positive-half spatial path
into its ordered outer boundary pair and its single strict-interior path.
It is assembled entirely from Mathlib's finite-product reindexing and splitting
measurable equivalences. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ≃ᵐ
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N) :=
  let X : Fin 2 ⊕ Fin H → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let reindex :=
    MeasurableEquiv.piCongrLeft X
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H)
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  let interior :=
    MeasurableEquiv.refl
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N)
  reindex.trans (split.trans (MeasurableEquiv.prodCongr pair interior))

/-- The complete positive-half spatial-path product Haar law is exactly the
product of pair-Haar on the two outer reflection boundaries and product Haar
on the `H` strict interior spatial slices.

No diagonal is replaced by an independent product: at `H = 1` the interior
factor remains the single central-slice Haar law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
        H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let X : Fin 2 ⊕ Fin H → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H
  let reindex := MeasurableEquiv.piCongrLeft X e
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  let interior :=
    MeasurableEquiv.refl
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N)
  let nested := MeasurableEquiv.prodCongr pair interior

  have hReindex :
      MeasurePreserving reindex
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
        (Measure.pi (fun _ : Fin 2 ⊕ Fin H => μ)) := by
    simpa [reindex, e, X,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Fin 2 ⊕ Fin H => μ) e)

  have hSplit :
      MeasurePreserving split
        (Measure.pi (fun _ : Fin 2 ⊕ Fin H => μ))
        ((Measure.pi (fun _ : Fin 2 => μ)).prod
          (Measure.pi (fun _ : Fin H => μ))) := by
    simpa [split, X] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : Fin 2 ⊕ Fin H => μ))

  have hPair :
      MeasurePreserving pair
        (Measure.pi (fun _ : Fin 2 => μ))
        (μ.prod μ) := by
    simpa [pair] using
      (MeasureTheory.measurePreserving_piFinTwo
        (fun _ : Fin 2 => μ))

  have hInterior :
      MeasurePreserving interior
        (Measure.pi (fun _ : Fin H => μ))
        (Measure.pi (fun _ : Fin H => μ)) := by
    simpa [interior] using
      (MeasurePreserving.id (Measure.pi (fun _ : Fin H => μ)))

  have hNested :
      MeasurePreserving nested
        ((Measure.pi (fun _ : Fin 2 => μ)).prod
          (Measure.pi (fun _ : Fin H => μ)))
        ((μ.prod μ).prod (Measure.pi (fun _ : Fin H => μ))) := by
    simpa [nested] using hPair.prod hInterior

  have hAll := (hReindex.trans hSplit).trans hNested
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    reindex, split, pair, interior, nested, X, e, μ] using hAll

end

end MathlibAnalytic
end MGAP4D
