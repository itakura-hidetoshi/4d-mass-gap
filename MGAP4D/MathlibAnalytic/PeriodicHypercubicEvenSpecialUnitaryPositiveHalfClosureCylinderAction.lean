import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfBoltzmannNormalization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCoordinateTransferBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFixedTimeClassification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance positiveHalfClosureCylinderActionSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩

local instance positiveHalfClosureCylinderActionSpatialVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureCylinderActionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Embed a spatial-slice link at an arbitrary Euclidean-time residue. -/
def periodicHypercubicEvenSpatialSliceLinkAtTime
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicEvenSpatialSliceVertexAtTime H t e.1, e.2.1)

/-- A spatial unit shift commutes with replacing only the Euclidean-time
coordinate. -/
theorem periodicHypercubicEvenSpatialSliceVertexAtTime_shift
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu : PeriodicHypercubicEvenSpatialDirection) :
    periodicHypercubicEvenSpatialSliceVertexAtTime H t
        (periodicHypercubicEvenSpatialSliceShift H v mu) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceVertexAtTime H t v) mu.1 := by
  funext i
  by_cases hi : i = 0
  · subst i
    have hmu0 : (0 : PeriodicHypercubicAxis) ≠ mu.1 := Ne.symm mu.2
    simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicShift_apply, hmu0]
  · simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenSpatialSliceShift,
      periodicHypercubicShift_apply, hi]

/-- Restrict an arbitrary four-dimensional configuration to the spatial links
of one Euclidean-time slice, canonically indexed by the primary-slice carrier. -/
def periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  fun e => A (periodicHypercubicEvenSpatialSliceLinkAtTime H t e)

/-- Embed a spatial-slice plaquette at an arbitrary Euclidean-time residue. -/
def periodicHypercubicEvenSpatialSlicePlaquetteAtTime
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    PeriodicHypercubicEvenPlaquette H :=
  (periodicHypercubicEvenSpatialSliceVertexAtTime H t p.1,
    ⟨(p.2.1.1.1, p.2.1.2.1), p.2.2⟩)

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteAtTime_firstAxis
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t p) = p.2.1.1.1 :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteAtTime_secondAxis
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t p) = p.2.1.2.1 :=
  rfl

/-- Spatial cells contain no Euclidean-time direction. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    ¬ periodicHypercubicEvenPlaquetteHasTimeDirection
      (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t p) := by
  intro h
  rcases h with h | h
  · exact p.2.1.1.2 h
  · exact p.2.1.2.2 h

/-- The intrinsic spatial-slice holonomy at time `t` is literally the
four-dimensional plaquette holonomy of the corresponding spatial cell. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restrictionAtTime_eq
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A t) p =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t p) := by
  unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
  unfold periodicHypercubicPlaquetteHolonomy
  unfold periodicHypercubicEvenSpatialSlicePlaquetteAtTime
  simp only [periodicHypercubicBoundaryStep_zero,
    periodicHypercubicBoundaryStep_one,
    periodicHypercubicBoundaryStep_two,
    periodicHypercubicBoundaryStep_three,
    periodicHypercubicStepValue]
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime
  unfold periodicHypercubicEvenSpatialSliceLinkAtTime
  rw [periodicHypercubicEvenSpatialSliceVertexAtTime_shift]
  rw [periodicHypercubicEvenSpatialSliceVertexAtTime_shift]
  rfl

/-- The Wilson energy of a spatial four-dimensional cell is therefore exactly
the intrinsic spatial-slice Wilson energy at that time. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteEnergy_restrictionAtTime_eq
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H t p)) =
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A t) p) := by
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restrictionAtTime_eq]

/-- Embed the time-space plaquette belonging to one positive-half cylinder slab
and one spatial link.  Since time axis `0` is the least coordinate axis, the
ordered plaquette axes are canonically `(0, μ)`. -/
def periodicHypercubicEvenPositiveHalfTemporalPlaquette
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenPlaquette H :=
  (periodicHypercubicEvenSpatialSliceVertexAtTime H
      (periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i) e.1,
    ⟨((0 : PeriodicHypercubicAxis), e.2.1),
      Fin.pos_iff_ne_zero.mpr e.2.2⟩)

@[simp] theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_firstAxis
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) = 0 :=
  rfl

@[simp] theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_secondAxis
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) = e.2.1 :=
  rfl

/-- Every cylinder temporal cell contains the Euclidean-time direction. -/
theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPlaquetteHasTimeDirection
      (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) :=
  Or.inl rfl

/-- Advancing one temporal link from the left endpoint of slab `i` reaches its
right endpoint at the same spatial vertex. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime_shift_time
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceVertexAtTime H
          (periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i) v) 0 =
      periodicHypercubicEvenSpatialSliceVertexAtTime H
        (periodicHypercubicEvenPositiveHalfCylinderSlabRightTime H i) v := by
  funext mu
  by_cases hmu : mu = 0
  · subst mu
    simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime,
      periodicHypercubicEvenPositiveHalfCylinderSlabRightTime,
      periodicHypercubicShift_apply]
  · simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicShift_apply, hmu]

/-- Read the spatial path of the positive cylinder directly from an arbitrary
four-dimensional link configuration. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N :=
  fun j =>
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
      ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))

/-- Read all positive-half temporal links directly from an arbitrary
four-dimensional link configuration. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N :=
  fun i v =>
    A (periodicHypercubicEvenPositiveHalfTemporalEdge H (i, v))

/-- The cylinder path at a slab's left endpoint is exactly the spatial
restriction at that slab time. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_castSucc
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A i.castSucc =
      periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
        (periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i) := by
  rfl

/-- The cylinder path at a slab's right endpoint is exactly the spatial
restriction at the next Euclidean-time slice. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_succ
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A i.succ =
      periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
        (periodicHypercubicEvenPositiveHalfCylinderSlabRightTime H i) := by
  rfl

/-- Exact holonomy word of one unfixed positive-half temporal cell. -/
theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_holonomy
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N A i e.1 *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A i.succ e *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N A i (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A i.castSucc e)⁻¹ := by
  unfold periodicHypercubicPlaquetteHolonomy
  unfold periodicHypercubicEvenPositiveHalfTemporalPlaquette
  simp only [periodicHypercubicBoundaryStep_zero,
    periodicHypercubicBoundaryStep_one,
    periodicHypercubicBoundaryStep_two,
    periodicHypercubicBoundaryStep_three,
    periodicHypercubicStepValue]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime
  unfold periodicHypercubicEvenSpatialSliceLinkAtTime
  unfold periodicHypercubicEvenPositiveHalfTemporalEdge
  rw [periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime_shift_time]
  rw [← periodicHypercubicEvenSpatialSliceVertexAtTime_shift]
  rfl

/-- The four-dimensional Wilson energy of one positive-half temporal plaquette
is exactly the corresponding local unfixed one-slab crossing energy.  The two
holonomy words differ only by conjugation by the lower spatial link, so no
commutativity of the gauge group is used. -/
theorem periodicHypercubicEvenPositiveHalfTemporalPlaquette_energy_eq_unfixed
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e)) =
      specialUnitaryWilsonPlaquetteEnergy N
        (((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
            H N A i.castSucc) e)⁻¹ *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
            H N A i) e.1 *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
            H N A i.succ) e *
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
            H N A i)
              (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹) := by
  rw [periodicHypercubicEvenPositiveHalfTemporalPlaquette_holonomy]
  let L :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
      H N A i.castSucc) e
  let W :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
        H N A i) e.1 *
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A i.succ) e *
      ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
        H N A i) (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ *
      L⁻¹
  have hconj := specialUnitaryWilsonPlaquetteEnergy_conjInvariant L⁻¹ W
  rw [inv_inv] at hconj
  rw [← hconj]
  congr 1
  dsimp [L, W]
  group

end

end MathlibAnalytic
end MGAP4D
