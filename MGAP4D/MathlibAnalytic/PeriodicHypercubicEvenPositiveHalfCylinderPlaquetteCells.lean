import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCylinderAction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingOpenHalfCharacterization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance positiveHalfCylinderPlaquetteCellsSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩

local instance positiveHalfCylinderPlaquetteCellsSpatialVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfCylinderPlaquetteCellsSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfCylinderPlaquetteCellsSpatialPlaquetteFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  Fintype.ofFinite _

/-- Plaquettes carrying the OS positive-half closure action: fixed-plane
spatial plaquettes, strict-positive plaquettes, and the two temporal boundary
layers adjacent to the fixed planes from the positive side. -/
def periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenSpatialCrossingPlaquette p ∨
    periodicHypercubicEvenStrictPositivePlaquette p ∨
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p

/-- Exact finite cell carrier of the positive half-cylinder.  There are `H+2`
spatial slices and `H+1` temporal slabs. -/
abbrev PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell
    (H : ℕ) : Type :=
  (Fin (H + 2) × PeriodicHypercubicEvenSpatialSlicePlaquette H) ⊕
    (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) ×
      PeriodicHypercubicEvenSpatialSliceLink H)

/-- Embed one positive-half cylinder cell into the actual four-dimensional
periodic plaquette carrier. -/
def periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H →
      PeriodicHypercubicEvenPlaquette H
  | Sum.inl z =>
      periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
        ((z.1.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) z.2
  | Sum.inr z =>
      periodicHypercubicEvenPositiveHalfTemporalPlaquette H z.1 z.2

@[simp] theorem periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val
    (H : ℕ)
    (j : Fin (H + 2))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    ((periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
        ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p).1 0).val =
      j.1 := by
  change
    (((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val = j.1
  apply ZMod.val_natCast_of_lt
  simp only [PeriodicHypercubicEvenSideLength]
  omega

@[simp] theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ((periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e).1 0).val = i.1 := by
  change
    ((periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i).val = i.1)
  unfold periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime
  apply ZMod.val_natCast_of_lt
  simp only [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount] at i ⊢
  omega

@[simp] theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_next_time_val
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (((periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e).1 0 + 1).val) =
      i.1 + 1 := by
  change
    ((periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i + 1).val =
      i.1 + 1)
  rw [show periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i + 1 =
      ((i.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) by
    simp [periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime]]
  apply ZMod.val_natCast_of_lt
  simp only [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount] at i ⊢
  omega

/-- Every spatial cylinder cell belongs to the OS positive-half closure
plaquette support.  The endpoint slices are spatial crossing cells; all
intermediate slices are strict-positive cells. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSpatialCell_supported
    (H : ℕ)
    (j : Fin (H + 2))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport
      (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
        ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p) := by
  let q := periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
    ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p
  have htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection q :=
    periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection
      H _ p
  by_cases hzero : j.1 = 0
  · left
    rw [periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane]
    refine ⟨htime, Or.inl ?_⟩
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane
    dsimp [q, periodicHypercubicEvenSpatialSlicePlaquetteAtTime]
    simpa [hzero]
  · by_cases hlast : j.1 = H + 1
    · left
      rw [periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane]
      refine ⟨htime, Or.inr ?_⟩
      unfold periodicHypercubicEvenOnAntipodalReflectionPlane
      dsimp [q, periodicHypercubicEvenSpatialSlicePlaquetteAtTime]
      simpa [hlast]
    · right
      left
      apply
        (periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
          q htime).2
      unfold periodicHypercubicEvenStrictPositiveVertex
      rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
      rw [show (q.1 0).val = j.1 by
        exact periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val H j p]
      omega

/-- Every temporal cylinder cell belongs to the same support.  The first and
last slabs are the positive boundary-temporal sectors; all strictly interior
slabs are strict-positive plaquettes. -/
theorem periodicHypercubicEvenPositiveHalfCylinderTemporalCell_supported
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport
      (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) := by
  let q := periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e
  have htime : periodicHypercubicEvenPlaquetteHasTimeDirection q :=
    periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection H i e
  have hi : i.1 < H + 1 := by
    simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using i.2
  by_cases hzero : i.1 = 0
  · right
    right
    refine ⟨htime, Or.inl ?_⟩
    simpa [q, hzero] using
      periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val H i e
  · by_cases hlast : i.1 = H
    · right
      right
      refine ⟨htime, Or.inr ?_⟩
      simpa [q, hlast] using
        periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val H i e
    · right
      left
      apply
        (periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
          q htime).2
      constructor
      · rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
        rw [show (q.1 0).val = i.1 by
          exact periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val H i e]
        omega
      · rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
        rw [show (q.1 0 + 1).val = i.1 + 1 by
          exact periodicHypercubicEvenPositiveHalfTemporalPlaquette_next_time_val H i e]
        omega

/-- The whole cylinder-cell embedding lands in the exact OS closure support. -/
theorem periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding_supported
    (H : ℕ)
    (c : PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H) :
    periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport
      (periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding H c) := by
  rcases c with z | z
  · exact periodicHypercubicEvenPositiveHalfCylinderSpatialCell_supported H z.1 z.2
  · exact periodicHypercubicEvenPositiveHalfCylinderTemporalCell_supported H z.1 z.2

/-- Forget the Euclidean-time coordinate of a purely spatial four-dimensional
plaquette. -/
def periodicHypercubicEvenSpatialSlicePlaquetteProjection
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    PeriodicHypercubicEvenSpatialSlicePlaquette H :=
  (periodicHypercubicEvenSpatialSliceVertexProjection H p.1,
    ⟨
      (⟨periodicHypercubicPlaquetteFirstAxis p,
          periodicHypercubicEvenPlaquetteFirstAxis_ne_zero_of_not_hasTimeDirection
            p htime⟩,
        ⟨periodicHypercubicPlaquetteSecondAxis p,
          periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_not_hasTimeDirection
            p htime⟩),
      p.2.2⟩)

/-- Restoring the original time coordinate after spatial projection reconstructs
the original purely spatial plaquette exactly. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteAtTime_projection
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenSpatialSlicePlaquetteAtTime H (p.1 0)
        (periodicHypercubicEvenSpatialSlicePlaquetteProjection H p htime) = p := by
  apply Prod.ext
  · exact periodicHypercubicEvenSpatialSliceVertexAtTime_projection H p.1
  · apply Subtype.ext
    rfl

/-- For an ordered time-containing plaquette, the first axis is necessarily
the Euclidean-time axis. -/
theorem periodicHypercubicEvenPlaquetteFirstAxis_eq_zero_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteFirstAxis p = 0 := by
  rcases htime with hfirst | hsecond
  · exact hfirst
  · have hlt := p.2.2
    change (periodicHypercubicPlaquetteFirstAxis p).val <
      (periodicHypercubicPlaquetteSecondAxis p).val at hlt
    have hcontra : (periodicHypercubicPlaquetteFirstAxis p).val < 0 := by
      simpa [hsecond] using hlt
    exact (Nat.not_lt_zero _ hcontra).elim

/-- The spatial axis of a time-containing ordered plaquette is nonzero. -/
theorem periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteSecondAxis p ≠ 0 := by
  intro hsecond
  have hfirst :=
    periodicHypercubicEvenPlaquetteFirstAxis_eq_zero_of_hasTimeDirection p htime
  have hlt := p.2.2
  change (periodicHypercubicPlaquetteFirstAxis p).val <
    (periodicHypercubicPlaquetteSecondAxis p).val at hlt
  have hcontra : (0 : ℕ) < 0 := by
    simpa [hfirst, hsecond] using hlt
  exact (Nat.lt_irrefl 0 hcontra)

/-- Forget time from the base vertex and retain the spatial axis of a temporal
plaquette. -/
def periodicHypercubicEvenTemporalPlaquetteSpatialLinkProjection
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    PeriodicHypercubicEvenSpatialSliceLink H :=
  (periodicHypercubicEvenSpatialSliceVertexProjection H p.1,
    ⟨periodicHypercubicPlaquetteSecondAxis p,
      periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_hasTimeDirection
        p htime⟩)

/-- A temporal plaquette is reconstructed from its base time and projected
spatial link. -/
theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_projection
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (hi : periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i = p.1 0) :
    periodicHypercubicEvenPositiveHalfTemporalPlaquette H i
        (periodicHypercubicEvenTemporalPlaquetteSpatialLinkProjection H p htime) = p := by
  apply Prod.ext
  · dsimp [periodicHypercubicEvenPositiveHalfTemporalPlaquette,
      periodicHypercubicEvenTemporalPlaquetteSpatialLinkProjection]
    rw [hi]
    exact periodicHypercubicEvenSpatialSliceVertexAtTime_projection H p.1
  · apply Subtype.ext
    apply Prod.ext
    · exact
        (periodicHypercubicEvenPlaquetteFirstAxis_eq_zero_of_hasTimeDirection
          p htime).symm
    · rfl

/-- Supported plaquettes as a finite subtype. -/
abbrev PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette
    (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport p}

/-- The cylinder-cell embedding with its support certificate attached. -/
def periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H →
      PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H :=
  fun c =>
    ⟨periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding H c,
      periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding_supported H c⟩

/-- Every supported plaquette has a unique cylinder-cell coordinate: spatial
cells use their base-time residue as one of the `H+2` slice indices, while
temporal cells use it as one of the `H+1` slab indices. -/
noncomputable def periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H →
      PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H := by
  classical
  intro q
  let p := q.1
  by_cases htime : periodicHypercubicEvenPlaquetteHasTimeDirection p
  · have hle : (p.1 0).val ≤ H := by
      rcases q.2 with hcross | hpos | hboundary
      · exact (hcross.2 htime).elim
      · have hbase :=
          (periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
            p htime).1 hpos |>.1
        exact
          ((periodicHypercubicEvenStrictPositiveTime_iff_val H (p.1 0)).1 hbase).2
      · rcases hboundary.2 with hzero | hH
        · dsimp [p]
          simpa only [hzero] using Nat.zero_le H
        · dsimp [p]
          simpa only [hH] using Nat.le_refl H
    let i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) :=
      ⟨(p.1 0).val, by
        simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using
          Nat.lt_succ_of_le hle⟩
    exact Sum.inr
      (i, periodicHypercubicEvenTemporalPlaquetteSpatialLinkProjection H p htime)
  · have hle : (p.1 0).val ≤ H + 1 := by
      rcases q.2 with hcross | hpos | hboundary
      · have hfixed :=
          (periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane p).1 hcross |>.2
        rcases hfixed with hprimary | hantipodal
        · unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hprimary
          rw [hprimary]
          simp
        · unfold periodicHypercubicEvenOnAntipodalReflectionPlane at hantipodal
          have hhalf_lt :
              H + 1 < PeriodicHypercubicEvenSideLength H := by
            change H + 1 < 2 * (H + 1)
            omega
          rw [hantipodal]
          simpa only [ZMod.val_natCast_of_lt hhalf_lt] using Nat.le_refl (H + 1)
      · have hbase :=
          (periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
            p htime).1 hpos
        unfold periodicHypercubicEvenStrictPositiveVertex at hbase
        exact
          ((periodicHypercubicEvenStrictPositiveTime_iff_val H (p.1 0)).1 hbase).2.trans
            (Nat.le_succ H)
      · exact (htime hboundary.1).elim
    let j : Fin (H + 2) := ⟨(p.1 0).val, Nat.lt_succ_of_le hle⟩
    exact Sum.inl
      (j, periodicHypercubicEvenSpatialSlicePlaquetteProjection H p htime)

/-- Re-embedding the recovered cylinder coordinate reconstructs every supported
plaquette. -/
theorem periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette_rightInverse
    (H : ℕ)
    (q : PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H) :
    periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette H
        (periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell H q) = q := by
  classical
  apply Subtype.ext
  by_cases htime : periodicHypercubicEvenPlaquetteHasTimeDirection q.1
  · simp only [periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell,
      htime, dif_pos,
      periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette,
      periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding]
    apply periodicHypercubicEvenPositiveHalfTemporalPlaquette_projection H q.1 htime
    unfold periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime
    exact ZMod.natCast_zmod_val (q.1.1 0)
  · simp only [periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell,
      htime, dif_neg,
      periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette,
      periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding]
    rw [ZMod.natCast_zmod_val (q.1.1 0)]
    exact periodicHypercubicEvenSpatialSlicePlaquetteAtTime_projection H q.1 htime

/-- Recovering coordinates after embedding a cylinder cell returns that cell. -/
theorem periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette_leftInverse
    (H : ℕ)
    (c : PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H) :
    periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell H
        (periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette H c) = c := by
  classical
  rcases c with z | z
  · rcases z with ⟨j, p⟩
    have htime :
        ¬ periodicHypercubicEvenPlaquetteHasTimeDirection
          (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
            ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p) :=
      periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection H _ p
    simp only [periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell,
      periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette,
      periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding,
      htime, dif_neg]
    apply congrArg Sum.inl
    apply Prod.ext
    · apply Fin.ext
      exact periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val H j p
    · apply Prod.ext
      · exact periodicHypercubicEvenSpatialSliceVertexProjection_atTime H _ p.1
      · apply Subtype.ext
        rfl
  · rcases z with ⟨i, e⟩
    have htime :
        periodicHypercubicEvenPlaquetteHasTimeDirection
          (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) :=
      periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection H i e
    simp only [periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell,
      periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette,
      periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding,
      htime, dif_pos]
    apply congrArg Sum.inr
    apply Prod.ext
    · apply Fin.ext
      exact periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val H i e
    · apply Prod.ext
      · exact periodicHypercubicEvenSpatialSliceVertexProjection_atTime H _ e.1
      · apply Subtype.ext
        rfl

/-- Exact finite equivalence between the geometric positive-half cylinder cells
and the plaquette support occurring in the OS positive-half closure action. -/
noncomputable def periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H ≃
      PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H where
  toFun := periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette H
  invFun := periodicHypercubicEvenPositiveHalfClosureSupportedPlaquetteToCell H
  left_inv := periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette_leftInverse H
  right_inv := periodicHypercubicEvenPositiveHalfCylinderCellToSupportedPlaquette_rightInverse H

end

end MathlibAnalytic
end MGAP4D
