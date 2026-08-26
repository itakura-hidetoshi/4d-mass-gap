import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCompletedPositiveActionPathSectors
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundarySpatialHalfWeightFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pure finite-slab bookkeeping for the symmetric spatial half-action.
The two reflection-fixed endpoint slices occur with coefficient `1/2`, while
every one of the `H` strict interior slices occurs exactly once.  The statement
is uniform in `H`, including `H = 0`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction_eq_endpoints_add_interior
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
        H N path =
      (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path 0) +
        (∑ k : Fin H,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path k.succ.castSucc)) +
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path (Fin.last H).succ) := by
  classical
  have hindex : ∀ k : Fin H, k.succ.castSucc = k.castSucc.succ := by
    intro k
    apply Fin.ext
    rfl
  have hinter :
      (∑ k : Fin H,
          (1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (path k.succ.castSucc)) +
        (∑ k : Fin H,
          (1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (path k.castSucc.succ)) =
      ∑ k : Fin H,
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (path k.succ.castSucc) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← hindex k]
    ring
  calc
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
        H N path =
      (∑ i : Fin (H + 1),
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path i.castSucc)) +
      (∑ i : Fin (H + 1),
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path i.succ)) := by
      simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction_eq_left_add_right
          H N path
    _ =
      ((1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N (path 0) +
        ∑ k : Fin H,
          (1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (path k.succ.castSucc)) +
      ((∑ k : Fin H,
          (1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (path k.castSucc.succ)) +
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path (Fin.last H).succ)) := by
      rw [Fin.sum_univ_succ]
      rw [Fin.sum_univ_castSucc]
      have hzero : (0 : Fin (H + 1)).castSucc = (0 : Fin (H + 2)) := by
        apply Fin.ext
        rfl
      simpa [hzero]
    _ =
      (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N (path 0) +
        ((∑ k : Fin H,
            (1 / 2 : ℝ) *
              periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
                (path k.succ.castSucc)) +
          (∑ k : Fin H,
            (1 / 2 : ℝ) *
              periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
                (path k.castSucc.succ))) +
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path (Fin.last H).succ) := by ring
    _ =
      (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N (path 0) +
        (∑ k : Fin H,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path k.succ.castSucc)) +
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path (Fin.last H).succ) := by rw [hinter]

/-- Restriction at time zero is literally the canonical primary spatial-slice
restriction. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime_zero
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A 0 =
      periodicHypercubicEvenSpatialSliceRestriction A := by
  funext e
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime
  unfold periodicHypercubicEvenSpatialSliceLinkAtTime
  unfold periodicHypercubicEvenSpatialSliceRestriction
  unfold periodicHypercubicEvenSpatialSliceLinkEmbedding
  congr 1
  apply Prod.ext
  · funext i
    by_cases hi : i = 0
    · subst i
      have he0 : e.1.1 0 = 0 := e.1.2
      simpa [periodicHypercubicEvenSpatialSliceVertexAtTime] using he0.symm
    · simp [periodicHypercubicEvenSpatialSliceVertexAtTime, hi]
  · rfl

/-- Restriction at time `H+1` is exactly the canonical antipodal spatial-slice
restriction obtained by half-period translation from the primary index. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime_antipodal
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
        (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) =
      periodicHypercubicEvenAntipodalSpatialSliceRestriction A := by
  funext e
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime
  unfold periodicHypercubicEvenSpatialSliceLinkAtTime
  unfold periodicHypercubicEvenAntipodalSpatialSliceRestriction
  congr 1
  apply Prod.ext
  · funext i
    by_cases hi : i = 0
    · subst i
      have he0 : e.1.1 0 = 0 := e.1.2
      simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
        periodicHypercubicEvenHalfPeriodTimeShift, he0]
    · simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
        periodicHypercubicEvenHalfPeriodTimeShift, hi]
  · rfl

/-- Along the spatial path extracted from an arbitrary four-dimensional
configuration, the strict interior path slice `k+1` is exactly the spatial
restriction at Euclidean time `k+1`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_interior
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : Fin H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A k.succ.castSucc =
      periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
        (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) := by
  rfl

/-- The primary endpoint of the extracted positive-half path is the canonical
primary fixed spatial slice. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_primary
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A 0 =
      periodicHypercubicEvenSpatialSliceRestriction A := by
  change
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A 0 =
      periodicHypercubicEvenSpatialSliceRestriction A
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime_zero H N A

/-- The terminal endpoint of the extracted positive-half path is the canonical
antipodal fixed spatial slice. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_antipodal
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A (Fin.last H).succ =
      periodicHypercubicEvenAntipodalSpatialSliceRestriction A := by
  change
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
        (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) =
      periodicHypercubicEvenAntipodalSpatialSliceRestriction A
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime_antipodal H N A

/-- For an arbitrary full four-dimensional configuration, the symmetric
spatial sector of the unfixed transfer path is precisely one half of the two
fixed-plane spatial crossing action plus the full action of every strict
positive interior spatial slice. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction_restriction_eq_halfSpatialCrossing_add_interior
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
        H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A) =
      (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        ∑ k : Fin H,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
              (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)))) := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction_eq_endpoints_add_interior]
  simp_rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_interior]
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_primary]
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_antipodal]
  rw [periodicHypercubicEvenSpatialCrossingWilsonAction_eq_primary_add_antipodal]
  ring

/-- Complete action-level identification.  The actual positive-half Wilson
bulk action, the positive-side boundary temporal action, and one half of the
purely-spatial fixed-plane crossing action are exactly the unfixed symmetric
`H+1`-slab path action extracted from the same four-dimensional configuration. -/
theorem periodicHypercubicEvenCompletePositiveHalfWilsonAction_eq_unfixedPathAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
        H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N A) := by
  let interior :=
    ∑ k : Fin H,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
          (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))))
  let temporal :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
      H N
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
        H N A)
  have hcompleted :=
    periodicHypercubicEvenCompletedPositiveWilsonAction_eq_interiorSpatial_add_temporalPath
      H N A
  have hspatial :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction_restriction_eq_halfSpatialCrossing_add_interior
      H N A
  have hpath :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction_eq_spatialHalf_add_temporal
      H N
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N A)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
        H N A)
  change
    (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A = _
  rw [hpath]
  change
    (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
          H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
            H N A) + temporal
  rw [hspatial]
  change
    (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      ((1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A + interior) +
        temporal
  change
    periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      interior + temporal at hcompleted
  linarith

/-- Exponentiating the complete action identity gives the exact pointwise
Boltzmann kernel identity before temporal gauge fixing. -/
theorem periodicHypercubicEvenCompletePositiveHalfBoltzmannWeight_eq_unfixedPathKernel
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp
        (-beta *
          ((1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
            periodicHypercubicEvenPositiveWilsonAction H N A +
            periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A)) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N A) := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_boltzmann]
  rw [← periodicHypercubicEvenCompletePositiveHalfWilsonAction_eq_unfixedPathAction]

end

end MathlibAnalytic
end MGAP4D