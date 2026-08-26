import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryPositiveHalfPathAmplitude
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySpatialSlicePair
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The purely spatial crossing plaquettes are precisely the plaquettes living
on one of the two reflection-fixed spatial slices. -/
abbrev PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenSpatialCrossingPlaquette p}

/-- Embed a primary-indexed spatial plaquette on the antipodal fixed slice by
the canonical half-period time translation. -/
def periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    PeriodicHypercubicEvenPlaquette H :=
  (periodicHypercubicEvenHalfPeriodTimeShift H p.1.1,
    ⟨(p.2.1.1.1, p.2.1.2.1), p.2.2⟩)

/-- The antipodal embedding contains no Euclidean-time direction. -/
theorem periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_not_hasTimeDirection
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    ¬ periodicHypercubicEvenPlaquetteHasTimeDirection
      (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p) := by
  intro htime
  rcases htime with htime | htime
  · exact p.2.1.1.2 htime
  · exact p.2.1.2.2 htime

/-- The antipodal embedding is based on the antipodal reflection plane. -/
theorem periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_onAntipodal
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenOnAntipodalReflectionPlane H
      (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p).1 := by
  unfold periodicHypercubicEvenOnAntipodalReflectionPlane
  rw [periodicHypercubicEvenHalfPeriodTimeShift_time, p.1.2]
  simp

/-- Hence every antipodal embedded spatial plaquette belongs to the spatial
crossing sector. -/
theorem periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_isSpatialCrossing
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialCrossingPlaquette
      (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p) := by
  rw [periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane]
  exact ⟨
    periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_not_hasTimeDirection H p,
    Or.inr
      (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_onAntipodal H p)⟩

/-- Read a spatial crossing plaquette as a plaquette on the primary fixed slice
or, after half-period reindexing, as a second copy of the same spatial-slice
plaquette carrier. -/
noncomputable def periodicHypercubicEvenSpatialCrossingPlaquetteToTwoSpatialSlices
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H →
      PeriodicHypercubicEvenSpatialSlicePlaquette H ⊕
        PeriodicHypercubicEvenSpatialSlicePlaquette H := by
  classical
  intro p
  have hgeom :=
    (periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane p.1).1 p.2
  have hmu : periodicHypercubicPlaquetteFirstAxis p.1 ≠ 0 :=
    periodicHypercubicEvenPlaquetteFirstAxis_ne_zero_of_not_hasTimeDirection
      p.1 hgeom.1
  have hnu : periodicHypercubicPlaquetteSecondAxis p.1 ≠ 0 :=
    periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_not_hasTimeDirection
      p.1 hgeom.1
  let dirs : PeriodicHypercubicEvenSpatialDirectionPair :=
    ⟨(⟨periodicHypercubicPlaquetteFirstAxis p.1, hmu⟩,
        ⟨periodicHypercubicPlaquetteSecondAxis p.1, hnu⟩), p.1.2.2⟩
  by_cases hp : periodicHypercubicEvenOnPrimaryReflectionPlane H p.1.1
  · exact Sum.inl (⟨p.1.1, hp⟩, dirs)
  · have ha : periodicHypercubicEvenOnAntipodalReflectionPlane H p.1.1 :=
      hgeom.2.resolve_left hp
    exact Sum.inr
      (periodicHypercubicEvenAntipodalToPrimarySpatialSliceVertex H ⟨p.1.1, ha⟩,
        dirs)

/-- Assemble either fixed-plane copy back into the four-dimensional spatial
crossing plaquette subtype. -/
def periodicHypercubicEvenTwoSpatialSlicesToSpatialCrossingPlaquette
    (H : ℕ) :
    (PeriodicHypercubicEvenSpatialSlicePlaquette H ⊕
      PeriodicHypercubicEvenSpatialSlicePlaquette H) →
      PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H
  | Sum.inl p =>
      ⟨periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p,
        periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_isSpatialCrossing H p⟩
  | Sum.inr p =>
      ⟨periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p,
        periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_isSpatialCrossing H p⟩

/-- Exact plaquette-level geometry: the spatial crossing sector is two copies
of the canonical spatial-slice plaquette carrier, one for each reflection-fixed
endpoint. -/
noncomputable def periodicHypercubicEvenSpatialCrossingPlaquetteEquivTwoSpatialSlices
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H ≃
      (PeriodicHypercubicEvenSpatialSlicePlaquette H ⊕
        PeriodicHypercubicEvenSpatialSlicePlaquette H) where
  toFun := periodicHypercubicEvenSpatialCrossingPlaquetteToTwoSpatialSlices H
  invFun := periodicHypercubicEvenTwoSpatialSlicesToSpatialCrossingPlaquette H
  left_inv p := by
    classical
    have hgeom :=
      (periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane p.1).1 p.2
    by_cases hp : periodicHypercubicEvenOnPrimaryReflectionPlane H p.1.1
    · apply Subtype.ext
      rfl
    · have ha : periodicHypercubicEvenOnAntipodalReflectionPlane H p.1.1 :=
        hgeom.2.resolve_left hp
      apply Subtype.ext
      apply Prod.ext
      · exact periodicHypercubicEvenHalfPeriodTimeShift_involutive H p.1.1
      · rfl
  right_inv z := by
    classical
    rcases z with p | p
    · have hp : periodicHypercubicEvenOnPrimaryReflectionPlane H
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p).1 :=
        periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_onPrimary H p
      simp [periodicHypercubicEvenSpatialCrossingPlaquetteToTwoSpatialSlices,
        periodicHypercubicEvenTwoSpatialSlicesToSpatialCrossingPlaquette, hp]
    · have ha : periodicHypercubicEvenOnAntipodalReflectionPlane H
        (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p).1 :=
        periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding_onAntipodal H p
      have hnp : ¬ periodicHypercubicEvenOnPrimaryReflectionPlane H
          (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p).1 := by
        intro hp
        exact periodicHypercubicEven_primary_antipodal_disjoint H
          (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p).1 hp ha
      simp [periodicHypercubicEvenSpatialCrossingPlaquetteToTwoSpatialSlices,
        periodicHypercubicEvenTwoSpatialSlicesToSpatialCrossingPlaquette,
        periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding,
        periodicHypercubicEvenAntipodalToPrimarySpatialSliceVertex,
        hnp]

/-- In particular the fixed-plane spatial plaquette sector has exactly twice
the cardinality of one spatial slice. -/
theorem periodicHypercubicEvenSpatialCrossingPlaquetteSubtype_card
    (H : ℕ) :
    Fintype.card (PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H) =
      2 * Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
  rw [Fintype.card_congr
    (periodicHypercubicEvenSpatialCrossingPlaquetteEquivTwoSpatialSlices H)]
  rw [Fintype.card_sum]
  omega

/-- The square root appearing in the OS Gram feature is exactly the half
Boltzmann weight of the fixed-plane spatial crossing action.  This is the
algebraic endpoint split needed before identifying the two fixed planes with
the two endpoint slice half-weights. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_sqrt_eq_halfAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.sqrt
        (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta b) =
      Real.exp
        (-(beta / 2) *
          periodicHypercubicEvenSpatialCrossingWilsonAction H N
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              b (fun _ => 1) (fun _ => 1))) := by
  unfold periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
  unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
  apply (Real.sqrt_eq_iff_eq_sq (Real.exp_nonneg _) (Real.exp_nonneg _)).2
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

end

end MathlibAnalytic
end MGAP4D
