import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveHalfOpenCoordinates
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfClosureFlatSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveHalfClosureFlatSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureFlatSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureFlatSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfClosureFlatSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfClosureFlatSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfClosureFlatSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfClosureFlatSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The exact flat spatial-path link index.  Time coordinate `0` is the primary
fixed slice, `H+1` is the antipodal fixed slice, and `1, ..., H` are the strict
positive interior spatial slices. -/
abbrev PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex (H : ℕ) : Type :=
  Fin (H + 2) × PeriodicHypercubicEvenSpatialSliceLink H

/-- The exact flat temporal-field index.  Its `H+1` layers are the temporal
links based at times `0, ..., H`. -/
abbrev PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldIndex (H : ℕ) : Type :=
  Fin (H + 1) × PeriodicHypercubicEvenSpatialSliceVertex H

/-- Flat coordinate index for the whole positive closure: all `H+2` spatial
slices together with all `H+1` forward temporal-link layers. -/
abbrev PeriodicHypercubicEvenPositiveHalfClosureFlatIndex (H : ℕ) : Type :=
  PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H ⊕
    PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldIndex H

/-- Before adding the temporal sector, the two fixed spatial slices and the
`H` strict interior spatial slices form exactly an `H+2`-slice path index. -/
abbrev PeriodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndex (H : ℕ) : Type :=
  (PeriodicHypercubicEvenSpatialSliceLink H ⊕
      PeriodicHypercubicEvenSpatialSliceLink H) ⊕
    (Fin H × PeriodicHypercubicEvenSpatialSliceLink H)

/-- Insert boundary/interior spatial coordinates into exact Euclidean-time
order `0,1,...,H,H+1`. -/
def periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndex H →
      PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H
  | Sum.inl (Sum.inl e) => (0, e)
  | Sum.inl (Sum.inr e) => (⟨H + 1, by omega⟩, e)
  | Sum.inr (k, e) => (⟨k.1 + 1, by omega⟩, e)

/-- Recover whether a spatial path layer is the primary boundary, antipodal
boundary, or one of the strict interior layers. -/
def periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H →
      PeriodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndex H :=
  fun z =>
    if h0 : z.1.1 = 0 then
      Sum.inl (Sum.inl z.2)
    else if hlast : z.1.1 = H + 1 then
      Sum.inl (Sum.inr z.2)
    else
      Sum.inr (⟨z.1.1 - 1, by omega⟩, z.2)

@[simp] theorem periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex_primary
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex H (0, e) =
      Sum.inl (Sum.inl e) := by
  simp [periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex]

@[simp] theorem periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex_antipodal
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex H
        (⟨H + 1, by omega⟩, e) =
      Sum.inl (Sum.inr e) := by
  simp [periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex]

@[simp] theorem periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex_interior
    (H : ℕ)
    (k : Fin H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex H
        (⟨k.1 + 1, by omega⟩, e) =
      Sum.inr (k, e) := by
  have hkLast : k.1 ≠ H := by omega
  simp [periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex, hkLast]

/-- The boundary/interior spatial decomposition is exactly equivalent to the
flat `H+2`-slice path index. -/
def periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndex H ≃
      PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H where
  toFun := periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath H
  invFun := periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex H
  left_inv z := by
    rcases z with (e | e) | z
    · simp [periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath]
    · simp [periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath]
    · rcases z with ⟨k, e⟩
      simp [periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath]
  right_inv z := by
    rcases z with ⟨j, e⟩
    by_cases h0 : j.1 = 0
    · have hj : j = 0 := Fin.ext h0
      rw [hj]
      simp [periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath]
    · by_cases hlast : j.1 = H + 1
      · have hj : j = ⟨H + 1, by omega⟩ := Fin.ext hlast
        rw [hj]
        simp [periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath]
      · have hjpos : 1 ≤ j.1 := by omega
        have hjle : j.1 ≤ H := by omega
        simp [periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex,
          periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
          h0, hlast]
        apply Fin.ext
        omega

/-- Reassociate the already-classified fixed and positive sectors so that all
spatial coordinates are grouped before the temporal coordinates. -/
def periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc
    (H : ℕ) :
    ((PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H) ⊕
      ((Fin H × PeriodicHypercubicEvenSpatialSliceLink H) ⊕
        PeriodicHypercubicEvenPositiveHalfTemporalIndex H)) ≃
      (PeriodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndex H ⊕
        PeriodicHypercubicEvenPositiveHalfTemporalIndex H) where
  toFun
    | Sum.inl b => Sum.inl (Sum.inl b)
    | Sum.inr (Sum.inl s) => Sum.inl (Sum.inr s)
    | Sum.inr (Sum.inr t) => Sum.inr t
  invFun
    | Sum.inl (Sum.inl b) => Sum.inl b
    | Sum.inl (Sum.inr s) => Sum.inr (Sum.inl s)
    | Sum.inr t => Sum.inr (Sum.inr t)
  left_inv z := by rcases z with z | (z | z) <;> rfl
  right_inv z := by rcases z with (z | z) | z <;> rfl

/-- Exact index equivalence from the actual positive closure
`FixedEdge ⊕ PositiveEdge` to

`(Fin (H+2) × SpatialSliceLink) ⊕
 (Fin (H+1) × SpatialSliceVertex)`.

This is the geometric coordinate statement needed before any temporal-gauge
change of variables. -/
noncomputable def periodicHypercubicEvenPositiveHalfClosureIndexEquiv
    (H : ℕ) :
    ((periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge) ≃
      PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H :=
  (Equiv.sumCongr
      (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H)
      (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H)).trans
    ((periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc H).trans
      (Equiv.sumCongr
        (periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv H)
        (Equiv.refl _)))

/-- Actual positive-closure data means the shared fixed boundary together with
the selected positive open half.  No negative-half coordinate is included. -/
abbrev PeriodicHypercubicEvenPositiveHalfClosureConfiguration
    (H : ℕ)
    (Value : Type*) :=
  (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value ×
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value

/-- Flat `H+2`-slice spatial-path field. -/
abbrev PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration
    (H : ℕ)
    (Value : Type*) :=
  PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H → Value

/-- Flat `H+1`-slab temporal-link field. -/
abbrev PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration
    (H : ℕ)
    (Value : Type*) :=
  PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldIndex H → Value

/-- Exact measurable equivalence from actual positive-closure coordinates to
flat spatial-path and temporal-link fields. -/
noncomputable def periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv
    (H : ℕ)
    (Value : Type*) [MeasurableSpace Value] :
    PeriodicHypercubicEvenPositiveHalfClosureConfiguration H Value ≃ᵐ
      (PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H Value ×
        PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H Value) :=
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ :
        (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
          (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge => Value)).symm).trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H => Value)
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H)).trans
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H => Value)))

/-- Product measure on actual positive-closure boundary/open-half coordinates. -/
noncomputable def periodicHypercubicEvenPositiveHalfClosurePiMeasure
    (H : ℕ)
    {Value : Type*} [MeasurableSpace Value]
    (mu : Measure Value) :
    Measure (PeriodicHypercubicEvenPositiveHalfClosureConfiguration H Value) :=
  ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure mu).prod
    ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure mu)

/-- Product measure on the flat `(H+2)` spatial-layer and `(H+1)` temporal-layer
coordinates. -/
noncomputable def periodicHypercubicEvenPositiveHalfClosureFlatCoordinatePiMeasure
    (H : ℕ)
    {Value : Type*} [MeasurableSpace Value]
    (mu : Measure Value) :
    Measure
      (PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H Value ×
        PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H Value) :=
  (Measure.pi
      (fun _ : PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H => mu)).prod
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldIndex H => mu))

/-- The exact positive-closure reindexing preserves every finite constant
product measure with sigma-finite one-link factor. -/
theorem periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv_measurePreserving
    (H : ℕ)
    {Value : Type*} [MeasurableSpace Value]
    (mu : Measure Value) [SigmaFinite mu] :
    MeasurePreserving
      (periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv H Value)
      (periodicHypercubicEvenPositiveHalfClosurePiMeasure H mu)
      (periodicHypercubicEvenPositiveHalfClosureFlatCoordinatePiMeasure H mu) := by
  let sourceIndex :=
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge
  let targetIndex := PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H
  let combine := (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : sourceIndex => Value)).symm
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : targetIndex => Value)
    (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H)
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : targetIndex => Value)
  have hCombine :
      MeasurePreserving combine
        (((periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure mu).prod
          ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure mu))
        (Measure.pi (fun _ : sourceIndex => mu)) := by
    simpa [sourceIndex, combine,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
        (fun _ : sourceIndex => mu))
  have hReindex :
      MeasurePreserving reindex
        (Measure.pi (fun _ : sourceIndex => mu))
        (Measure.pi (fun _ : targetIndex => mu)) := by
    simpa [sourceIndex, targetIndex, reindex] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : targetIndex => mu)
        (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H))
  have hSplit :
      MeasurePreserving split
        (Measure.pi (fun _ : targetIndex => mu))
        ((Measure.pi
            (fun _ : PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H => mu)).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldIndex H => mu))) := by
    simpa [targetIndex, split] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : targetIndex => mu))
  simpa [periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosurePiMeasure,
    periodicHypercubicEvenPositiveHalfClosureFlatCoordinatePiMeasure,
    sourceIndex, targetIndex, combine, reindex, split] using
    (hCombine.trans hReindex).trans hSplit

/-- Normalized compact `SU(N)` Haar measure on actual positive-closure
boundary/open-half coordinates. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure
    (H N : ℕ) :
    Measure
      (PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  periodicHypercubicEvenPositiveHalfClosurePiMeasure H
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Normalized compact `SU(N)` Haar product on all flat `H+2` spatial layers
and `H+1` temporal-link layers. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure
    (H N : ℕ) :
    Measure
      (PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  periodicHypercubicEvenPositiveHalfClosureFlatCoordinatePiMeasure H
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- The actual positive closure is exactly normalized Haar on the flat
`(H+2)`-slice spatial path times normalized Haar on the `(H+1)` temporal-link
layers.  This is a pure coordinate/Haar statement; no gauge fixing is used. -/
theorem periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv_measurePreserving_haar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure H N) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure] using
    (periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv_measurePreserving
      H (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

end

end MathlibAnalytic
end MGAP4D