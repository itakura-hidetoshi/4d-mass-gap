import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveHalfPlaquetteSectorClassification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCylinderAction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance positiveHalfPlaquetteCoordinatesSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- Subtype of actual four-dimensional plaquettes lying on one of the strict
positive interior spatial slices. -/
abbrev PeriodicHypercubicEvenPositiveHalfSpatialPlaquetteSubtype (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenPositiveHalfSpatialPlaquette p}

/-- Subtype of actual four-dimensional time-space plaquettes lying in one of
the `H+1` complete positive-half cylinder slabs. -/
abbrev PeriodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteSubtype
    (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette p}

/-- At any fixed Euclidean-time residue, the spatial-slice plaquette embedding
is injective. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteAtTime_injective
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    Function.Injective (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    have hbase := congrArg Prod.fst h
    have hproj := congrArg
      (periodicHypercubicEvenSpatialSliceVertexProjection H) hbase
    simpa [periodicHypercubicEvenSpatialSlicePlaquetteAtTime] using hproj
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun r => periodicHypercubicPlaquetteFirstAxis r) h
    · apply Subtype.ext
      exact congrArg (fun r => periodicHypercubicPlaquetteSecondAxis r) h

/-- Put an intrinsic spatial plaquette on the strict-positive slice indexed by
`k : Fin H`.  The time convention is `k ↦ k+1`. -/
def periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates
    (H : ℕ)
    (z : Fin H × PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    PeriodicHypercubicEvenPositiveHalfSpatialPlaquetteSubtype H := by
  let t : ZMod (PeriodicHypercubicEvenSideLength H) :=
    ((z.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))
  refine ⟨periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t z.2, ?_⟩
  rw [periodicHypercubicEvenPositiveHalfSpatialPlaquette_iff_baseTime_val]
  refine ⟨periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection
    H t z.2, ?_⟩
  have ht : z.1.1 + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  change 1 ≤ t.val ∧ t.val ≤ H
  dsimp [t]
  rw [ZMod.val_natCast_of_lt ht]
  omega

/-- Distinct interior slice/plaquette coordinates give distinct actual
four-dimensional spatial plaquettes. -/
theorem periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates_injective
    (H : ℕ) :
    Function.Injective
      (periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates H) := by
  intro z w h
  have hp := congrArg Subtype.val h
  have htime := congrArg
    (fun p : PeriodicHypercubicEvenPlaquette H => (p.1 0).val) hp
  have hzlt : z.1.1 + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hwlt : w.1.1 + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hknat : z.1.1 = w.1.1 := by
    change
      (((z.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val =
        (((w.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val at htime
    rw [ZMod.val_natCast_of_lt hzlt, ZMod.val_natCast_of_lt hwlt] at htime
    omega
  have hk : z.1 = w.1 := Fin.ext hknat
  apply Prod.ext
  · exact hk
  · change
      periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
          (((z.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) z.2 =
        periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
          (((w.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) w.2 at hp
    rw [hk] at hp
    exact periodicHypercubicEvenSpatialSlicePlaquetteAtTime_injective
      H (((w.1.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) hp

/-- Every actual strict-positive purely-spatial plaquette is uniquely obtained
from one interior slice and one intrinsic spatial-slice plaquette. -/
theorem periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates_surjective
    (H : ℕ) :
    Function.Surjective
      (periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates H) := by
  intro q
  have hq :=
    (periodicHypercubicEvenPositiveHalfSpatialPlaquette_iff_baseTime_val q.1).1 q.2
  let k : Fin H := ⟨(q.1.1 0).val - 1, by omega⟩
  let v0 := periodicHypercubicEvenSpatialSliceVertexProjection H q.1.1
  let mu : PeriodicHypercubicEvenSpatialDirection :=
    ⟨periodicHypercubicPlaquetteFirstAxis q.1,
      periodicHypercubicEvenPlaquetteFirstAxis_ne_zero_of_not_hasTimeDirection
        q.1 hq.1⟩
  let nu : PeriodicHypercubicEvenSpatialDirection :=
    ⟨periodicHypercubicPlaquetteSecondAxis q.1,
      periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_not_hasTimeDirection
        q.1 hq.1⟩
  let p : PeriodicHypercubicEvenSpatialSlicePlaquette H :=
    (v0, ⟨(mu, nu), q.1.2.2⟩)
  refine ⟨(k, p), ?_⟩
  apply Subtype.ext
  change
    periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
        (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) p = q.1
  apply Prod.ext
  · dsimp [p]
    change
      periodicHypercubicEvenSpatialSliceVertexAtTime H
          (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) v0 = q.1.1
    have hkval : k.1 + 1 = (q.1.1 0).val := by
      dsimp [k]
      omega
    have hcast :
        (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) = q.1.1 0 := by
      rw [hkval]
      exact ZMod.natCast_zmod_val _
    rw [hcast]
    simpa [v0] using periodicHypercubicEvenSpatialSliceVertexAtTime_projection H q.1.1
  · apply Subtype.ext
    apply Prod.ext <;> rfl

/-- Exact finite coordinate equivalence for the strict-positive purely-spatial
plaquette sector. -/
noncomputable def periodicHypercubicEvenPositiveHalfSpatialPlaquetteCoordinateEquiv
    (H : ℕ) :
    (Fin H × PeriodicHypercubicEvenSpatialSlicePlaquette H) ≃
      PeriodicHypercubicEvenPositiveHalfSpatialPlaquetteSubtype H :=
  Equiv.ofBijective
    (periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates H)
    ⟨periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates_injective H,
      periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates_surjective H⟩

/-- Put a spatial link into the time-space plaquette of one complete
positive-half slab, using the canonical existing slab plaquette embedding. -/
def periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates
    (H : ℕ)
    (z : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) ×
      PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteSubtype H := by
  refine ⟨periodicHypercubicEvenPositiveHalfTemporalPlaquette H z.1 z.2, ?_⟩
  rw [periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette_iff_baseTime_val_le]
  refine ⟨periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection
    H z.1 z.2, ?_⟩
  change (periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H z.1).val ≤ H
  unfold periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime
  have hzlt : z.1.1 < PeriodicHypercubicEvenSideLength H := by
    have hz := z.1.2
    simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount,
      PeriodicHypercubicEvenSideLength] at hz ⊢
    omega
  rw [ZMod.val_natCast_of_lt hzlt]
  have hz := z.1.2
  simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount] at hz
  omega

/-- The canonical slab temporal plaquette embedding is injective jointly in
its slab and spatial-link coordinates. -/
theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_coordinates_injective
    (H : ℕ) :
    Function.Injective
      (fun z : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) ×
          PeriodicHypercubicEvenSpatialSliceLink H =>
        periodicHypercubicEvenPositiveHalfTemporalPlaquette H z.1 z.2) := by
  intro z w h
  have htime := congrArg
    (fun p : PeriodicHypercubicEvenPlaquette H => (p.1 0).val) h
  have hzlt : z.1.1 < PeriodicHypercubicEvenSideLength H := by
    have hz := z.1.2
    simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount,
      PeriodicHypercubicEvenSideLength] at hz ⊢
    omega
  have hwlt : w.1.1 < PeriodicHypercubicEvenSideLength H := by
    have hw := w.1.2
    simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount,
      PeriodicHypercubicEvenSideLength] at hw ⊢
    omega
  have hinat : z.1.1 = w.1.1 := by
    change
      ((periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H z.1).val) =
        ((periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H w.1).val) at htime
    unfold periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime at htime
    rw [ZMod.val_natCast_of_lt hzlt, ZMod.val_natCast_of_lt hwlt] at htime
    exact htime
  have hi : z.1 = w.1 := Fin.ext hinat
  apply Prod.ext
  · exact hi
  · apply Prod.ext
    · apply Subtype.ext
      have hbase := congrArg Prod.fst h
      have hproj := congrArg
        (periodicHypercubicEvenSpatialSliceVertexProjection H) hbase
      simpa [periodicHypercubicEvenPositiveHalfTemporalPlaquette] using hproj
    · apply Subtype.ext
      exact congrArg (fun p => periodicHypercubicPlaquetteSecondAxis p) h

/-- The subtype-valued temporal coordinate map is injective. -/
theorem periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates_injective
    (H : ℕ) :
    Function.Injective
      (periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates H) := by
  intro z w h
  exact periodicHypercubicEvenPositiveHalfTemporalPlaquette_coordinates_injective H
    (congrArg Subtype.val h)

/-- Every complete-positive-half temporal plaquette is uniquely one of the
canonical `(slab, spatial link)` plaquettes. -/
theorem periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates_surjective
    (H : ℕ) :
    Function.Surjective
      (periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates H) := by
  intro q
  have hq :=
    (periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette_iff_baseTime_val_le q.1).1 q.2
  let i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) :=
    ⟨(q.1.1 0).val, by
      simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
      omega⟩
  let v0 := periodicHypercubicEvenSpatialSliceVertexProjection H q.1.1
  let mu : PeriodicHypercubicEvenSpatialDirection :=
    ⟨periodicHypercubicPlaquetteSecondAxis q.1,
      periodicHypercubicPlaquetteSecondAxis_ne_zero q.1⟩
  let e : PeriodicHypercubicEvenSpatialSliceLink H := (v0, mu)
  refine ⟨(i, e), ?_⟩
  apply Subtype.ext
  change periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e = q.1
  apply Prod.ext
  · dsimp [e]
    change
      periodicHypercubicEvenSpatialSliceVertexAtTime H
          (periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i) v0 = q.1.1
    have hcast :
        periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i = q.1.1 0 := by
      unfold periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime
      dsimp [i]
      exact ZMod.natCast_zmod_val _
    rw [hcast]
    simpa [v0] using periodicHypercubicEvenSpatialSliceVertexAtTime_projection H q.1.1
  · apply Subtype.ext
    apply Prod.ext
    · have hfirst :=
        (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero q.1).1 hq.1
      exact hfirst.symm
    · rfl

/-- Exact finite coordinate equivalence for all `H+1` temporal plaquette
layers of the complete positive half-cylinder. -/
noncomputable def periodicHypercubicEvenPositiveHalfTemporalPlaquetteCoordinateEquiv
    (H : ℕ) :
    (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) ×
        PeriodicHypercubicEvenSpatialSliceLink H) ≃
      PeriodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteSubtype H :=
  Equiv.ofBijective
    (periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates H)
    ⟨periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates_injective H,
      periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates_surjective H⟩

end

end MathlibAnalytic
end MGAP4D
