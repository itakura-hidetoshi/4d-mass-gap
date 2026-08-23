import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySpatialSlicePair
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfOpenCoordinatesSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveHalfOpenCoordinatesSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfOpenCoordinatesSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfOpenCoordinatesSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfOpenCoordinatesSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfOpenCoordinatesSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfOpenCoordinatesSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfOpenCoordinatesSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Replace only the Euclidean-time coordinate of a primary-slice vertex.
The spatial coordinates are left unchanged. -/
def periodicHypercubicEvenSpatialSliceVertexAtTime
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    PeriodicHypercubicEvenVertex H :=
  fun i => if i = 0 then t else v.1 i

@[simp] theorem periodicHypercubicEvenSpatialSliceVertexAtTime_time
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpatialSliceVertexAtTime H t v 0 = t := by
  simp [periodicHypercubicEvenSpatialSliceVertexAtTime]

@[simp] theorem periodicHypercubicEvenSpatialSliceVertexAtTime_space
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    {i : PeriodicHypercubicAxis}
    (hi : i ≠ 0) :
    periodicHypercubicEvenSpatialSliceVertexAtTime H t v i = v.1 i := by
  simp [periodicHypercubicEvenSpatialSliceVertexAtTime, hi]

/-- Forget the time coordinate of an arbitrary four-dimensional vertex while
retaining all spatial coordinates. -/
def periodicHypercubicEvenSpatialSliceVertexProjection
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  ⟨fun i => if i = 0 then 0 else v i, by
    simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩

@[simp] theorem periodicHypercubicEvenSpatialSliceVertexProjection_atTime
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpatialSliceVertexProjection H
        (periodicHypercubicEvenSpatialSliceVertexAtTime H t v) = v := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    exact v.2.symm
  · simp [periodicHypercubicEvenSpatialSliceVertexProjection,
      periodicHypercubicEvenSpatialSliceVertexAtTime, hi]

@[simp] theorem periodicHypercubicEvenSpatialSliceVertexAtTime_projection
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialSliceVertexAtTime H (v 0)
        (periodicHypercubicEvenSpatialSliceVertexProjection H v) = v := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp
  · simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenSpatialSliceVertexProjection, hi]

/-- Spatial links in the strict positive interior slices `1, ..., H`, indexed
by the modern primary-slice link carrier after forgetting the time coordinate. -/
abbrev PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex (H : ℕ) : Type :=
  Fin H × PeriodicHypercubicEvenSpatialSliceLink H

/-- Positive temporal links based at slices `0, ..., H`, indexed by their
spatial vertex and slab number. -/
abbrev PeriodicHypercubicEvenPositiveHalfTemporalIndex (H : ℕ) : Type :=
  Fin (H + 1) × PeriodicHypercubicEvenSpatialSliceVertex H

/-- Exact disjoint geometric index for the open positive half: interior spatial
links together with all forward temporal links between the two fixed slices. -/
abbrev PeriodicHypercubicEvenPositiveHalfOpenIndex (H : ℕ) : Type :=
  PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H ⊕
    PeriodicHypercubicEvenPositiveHalfTemporalIndex H

/-- Embed an interior spatial-layer index into the actual four-dimensional edge
carrier.  `k : Fin H` represents source time `k+1`. -/
def periodicHypercubicEvenPositiveHalfInteriorSpatialEdge
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H) :
    PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicEvenSpatialSliceVertexAtTime H
      (((z.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) z.2.1,
    z.2.2.1)

/-- Embed a temporal-layer index into the actual four-dimensional edge carrier.
`k : Fin (H+1)` represents the temporal link based at source time `k`. -/
def periodicHypercubicEvenPositiveHalfTemporalEdge
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfTemporalIndex H) :
    PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicEvenSpatialSliceVertexAtTime H
      (((z.1.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) z.2,
    0)

@[simp] theorem periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_time_val
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H) :
    ((periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H z).1 0).val =
      z.1.1 + 1 := by
  change ((((z.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val =
    z.1.1 + 1)
  apply ZMod.val_natCast_of_lt
  simp only [PeriodicHypercubicEvenSideLength]
  omega

@[simp] theorem periodicHypercubicEvenPositiveHalfTemporalEdge_time_val
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfTemporalIndex H) :
    ((periodicHypercubicEvenPositiveHalfTemporalEdge H z).1 0).val =
      z.1.1 := by
  change ((((z.1.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val =
    z.1.1)
  apply ZMod.val_natCast_of_lt
  simp only [PeriodicHypercubicEvenSideLength]
  omega

/-- Every interior spatial-layer coordinate lies in the selected positive edge
sector. -/
theorem periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_positive
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H z) =
      ReflectionEdgeSide.positive := by
  apply periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
  · exact z.2.2.2
  · rw [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_time_val]
    omega
  · rw [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_time_val]
    omega

/-- Every temporal-layer coordinate lies in the selected positive edge sector. -/
theorem periodicHypercubicEvenPositiveHalfTemporalEdge_positive
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfTemporalIndex H) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenPositiveHalfTemporalEdge H z) =
      ReflectionEdgeSide.positive := by
  change periodicHypercubicEvenEdgeSide H
      ((periodicHypercubicEvenPositiveHalfTemporalEdge H z).1, 0) =
    ReflectionEdgeSide.positive
  apply periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
  rw [periodicHypercubicEvenPositiveHalfTemporalEdge_time_val]
  omega

/-- The interior-spatial embedding is injective: source time recovers the layer,
and projection back to time zero recovers the spatial link. -/
theorem periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_injective
    (H : ℕ) :
    Function.Injective (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H) := by
  intro z w h
  have htime := congrArg
    (fun e : PeriodicHypercubicEvenEdge H => (e.1 0).val) h
  have hkNat : z.1.1 + 1 = w.1.1 + 1 := by
    simpa only [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_time_val] using htime
  have hk : z.1 = w.1 := by
    apply Fin.ext
    omega
  have hsource := congrArg
    (fun e : PeriodicHypercubicEvenEdge H => e.1) h
  have hvertex : z.2.1 = w.2.1 := by
    have hp := congrArg
      (periodicHypercubicEvenSpatialSliceVertexProjection H) hsource
    simpa [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge] using hp
  have hdirectionRaw := congrArg
    (fun e : PeriodicHypercubicEvenEdge H => e.2) h
  have hdirection : z.2.2 = w.2.2 := by
    apply Subtype.ext
    simpa [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge] using hdirectionRaw
  apply Prod.ext
  · exact hk
  · apply Prod.ext
    · exact hvertex
    · exact hdirection

/-- The temporal-layer embedding is injective. -/
theorem periodicHypercubicEvenPositiveHalfTemporalEdge_injective
    (H : ℕ) :
    Function.Injective (periodicHypercubicEvenPositiveHalfTemporalEdge H) := by
  intro z w h
  have htime := congrArg
    (fun e : PeriodicHypercubicEvenEdge H => (e.1 0).val) h
  have hkNat : z.1.1 = w.1.1 := by
    simpa only [periodicHypercubicEvenPositiveHalfTemporalEdge_time_val] using htime
  have hk : z.1 = w.1 := Fin.ext hkNat
  have hsource := congrArg
    (fun e : PeriodicHypercubicEvenEdge H => e.1) h
  have hvertex : z.2 = w.2 := by
    have hp := congrArg
      (periodicHypercubicEvenSpatialSliceVertexProjection H) hsource
    simpa [periodicHypercubicEvenPositiveHalfTemporalEdge] using hp
  apply Prod.ext
  · exact hk
  · exact hvertex

/-- Spatial and temporal coordinate images are disjoint because their edge
directions are respectively nonzero and zero. -/
theorem periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_ne_temporalEdge
    (H : ℕ)
    (z : PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H)
    (w : PeriodicHypercubicEvenPositiveHalfTemporalIndex H) :
    periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H z ≠
      periodicHypercubicEvenPositiveHalfTemporalEdge H w := by
  intro h
  have hdirection := congrArg
    (fun e : PeriodicHypercubicEvenEdge H => e.2) h
  exact z.2.2.2 (by
    simpa [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge,
      periodicHypercubicEvenPositiveHalfTemporalEdge] using hdirection)

/-- Assemble the geometric sum index into the actual selected positive edge
sector. -/
def periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfOpenIndex H →
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge
  | Sum.inl z =>
      ⟨periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H z,
        periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_positive H z⟩
  | Sum.inr z =>
      ⟨periodicHypercubicEvenPositiveHalfTemporalEdge H z,
        periodicHypercubicEvenPositiveHalfTemporalEdge_positive H z⟩

/-- The assembled positive-half geometric index loses no information. -/
theorem periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge_injective
    (H : ℕ) :
    Function.Injective
      (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H) := by
  intro z w h
  rcases z with z | z <;> rcases w with w | w
  · congr 1
    exact periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_injective H
      (congrArg Subtype.val h)
  · exact False.elim
      (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_ne_temporalEdge
        H z w (congrArg Subtype.val h))
  · exact False.elim
      (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_ne_temporalEdge
        H w z (congrArg Subtype.val h).symm)
  · congr 1
    exact periodicHypercubicEvenPositiveHalfTemporalEdge_injective H
      (congrArg Subtype.val h)

/-- Every actual selected positive edge is either a spatial link based at one of
the strict interior times `1, ..., H`, or a temporal link based at one of the
slab times `0, ..., H`. -/
theorem periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge_surjective
    (H : ℕ) :
    Function.Surjective
      (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H) := by
  intro e
  have hepos :
      periodicHypercubicEvenEdgeSide H e.1 = ReflectionEdgeSide.positive := by
    simpa [periodicHypercubicEvenEdgeOrbitPartition] using e.2
  by_cases htime : e.1.2 = 0
  · have hedge : e.1 = (e.1.1, 0) := by
      apply Prod.ext
      · rfl
      · exact htime
    have hle : (e.1.1 0).val ≤ H := by
      by_contra hnot
      have hhalf : H + 1 ≤ (e.1.1 0).val := by omega
      have hneg :=
        periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
          H e.1.1 hhalf
      rw [← hedge, hepos] at hneg
      cases hneg
    let k : Fin (H + 1) := ⟨(e.1.1 0).val, by omega⟩
    let v0 := periodicHypercubicEvenSpatialSliceVertexProjection H e.1.1
    refine ⟨Sum.inr (k, v0), ?_⟩
    apply Subtype.ext
    change periodicHypercubicEvenPositiveHalfTemporalEdge H (k, v0) = e.1
    apply Prod.ext
    · change periodicHypercubicEvenSpatialSliceVertexAtTime H
          (((k.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) v0 = e.1.1
      have hcast :
          (((k.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) = e.1.1 0 := by
        dsimp [k]
        exact ZMod.natCast_zmod_val _
      rw [hcast]
      simpa [v0] using
        periodicHypercubicEvenSpatialSliceVertexAtTime_projection H e.1.1
    · simpa [periodicHypercubicEvenPositiveHalfTemporalEdge] using htime.symm
  · have hzero : (e.1.1 0).val ≠ 0 := by
      intro hz
      have hfixed :=
        periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
          H e.1 htime hz
      rw [hepos] at hfixed
      cases hfixed
    have hpos : 1 ≤ (e.1.1 0).val := Nat.one_le_iff_ne_zero.2 hzero
    have hle : (e.1.1 0).val ≤ H := by
      by_contra hnot
      have hhalf : H + 1 ≤ (e.1.1 0).val := by omega
      exact
        (periodicHypercubicEvenEdgeSide_spatial_ne_positive_of_zero_or_half_le_val
          H e.1 htime (Or.inr hhalf)) hepos
    let k : Fin H := ⟨(e.1.1 0).val - 1, by omega⟩
    let v0 := periodicHypercubicEvenSpatialSliceVertexProjection H e.1.1
    let mu : PeriodicHypercubicEvenSpatialDirection := ⟨e.1.2, htime⟩
    have hk : k.1 + 1 = (e.1.1 0).val := by
      dsimp [k]
      omega
    refine ⟨Sum.inl (k, (v0, mu)), ?_⟩
    apply Subtype.ext
    change periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H
        (k, (v0, mu)) = e.1
    apply Prod.ext
    · change periodicHypercubicEvenSpatialSliceVertexAtTime H
          (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) v0 = e.1.1
      have hcast :
          (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) = e.1.1 0 := by
        rw [hk]
        exact ZMod.natCast_zmod_val _
      rw [hcast]
      simpa [v0] using
        periodicHypercubicEvenSpatialSliceVertexAtTime_projection H e.1.1
    · rfl

/-- Exact geometric index equivalence for the actual selected positive edge
sector:

`PositiveEdge ≃ (Fin H × SpatialSliceLink) ⊕
                (Fin (H+1) × SpatialSliceVertex)`.

The first summand is the `H` strict interior spatial slices and the second is
the `H+1` temporal-link layers. -/
noncomputable def periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex
    (H : ℕ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge ≃
      PeriodicHypercubicEvenPositiveHalfOpenIndex H :=
  (Equiv.ofBijective
    (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H)
    ⟨periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge_injective H,
      periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge_surjective H⟩).symm

/-- Measurable coordinate equivalence from the actual open positive half to its
interior-spatial and temporal-layer fields. -/
noncomputable def periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv
    (H : ℕ)
    (Value : Type*) [MeasurableSpace Value] :
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value ≃ᵐ
      ((PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H → Value) ×
        (PeriodicHypercubicEvenPositiveHalfTemporalIndex H → Value)) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => Value)
      (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H)).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => Value))

/-- Product measure on the exact interior-spatial/temporal coordinate pair. -/
noncomputable def periodicHypercubicEvenPositiveHalfOpenCoordinatePiMeasure
    (H : ℕ)
    {Value : Type*} [MeasurableSpace Value]
    (mu : Measure Value) :
    Measure
      ((PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H → Value) ×
        (PeriodicHypercubicEvenPositiveHalfTemporalIndex H → Value)) :=
  (Measure.pi
      (fun _ : PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H => mu)).prod
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenPositiveHalfTemporalIndex H => mu))

/-- Reindexing the actual positive open half into spatial and temporal layers
preserves every finite constant product measure with sigma-finite one-link
factor. -/
theorem periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv_measurePreserving
    (H : ℕ)
    {Value : Type*} [MeasurableSpace Value]
    (mu : Measure Value) [SigmaFinite mu] :
    MeasurePreserving
      (periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv H Value)
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure mu)
      (periodicHypercubicEvenPositiveHalfOpenCoordinatePiMeasure H mu) := by
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => Value)
    (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H)
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => Value)
  have hReindex :
      MeasurePreserving reindex
        ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure mu)
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => mu)) := by
    simpa [reindex, FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => mu)
        (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H))
  have hSplit :
      MeasurePreserving split
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => mu))
        ((Measure.pi
            (fun _ : PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H => mu)).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenPositiveHalfTemporalIndex H => mu))) := by
    simpa [split] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : PeriodicHypercubicEvenPositiveHalfOpenIndex H => mu))
  simpa [periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfOpenCoordinatePiMeasure, reindex, split] using
    hReindex.trans hSplit

/-- Normalized compact `SU(N)` Haar product measure on the exact positive-half
spatial/temporal coordinate pair. -/
noncomputable def periodicHypercubicEvenPositiveHalfOpenCoordinateHaarMeasure
    (H N : ℕ) :
    Measure
      ((PeriodicHypercubicEvenPositiveHalfInteriorSpatialIndex H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        (PeriodicHypercubicEvenPositiveHalfTemporalIndex H →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  periodicHypercubicEvenPositiveHalfOpenCoordinatePiMeasure H
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- The actual Wilson positive-open-half Haar measure is exactly product Haar
on the `H` interior spatial layers and the `H+1` temporal-link layers after the
canonical geometric reindexing. -/
theorem periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv_measurePreserving_haar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)
      (periodicHypercubicEvenPositiveHalfOpenCoordinateHaarMeasure H N) := by
  simpa [periodicHypercubicEvenOpenHalfHaarMeasure,
    periodicHypercubicEvenPositiveHalfOpenCoordinateHaarMeasure] using
    (periodicHypercubicEvenPositiveHalfOpenMeasurableEquiv_measurePreserving
      H (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

end

end MathlibAnalytic
end MGAP4D
