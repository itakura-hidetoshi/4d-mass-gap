import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalFiberedRelativeTrace
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteFixedEdges

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical primary-side temporal plaquette attached to a spatial edge whose
source lies on the primary fixed slice.  The ordered axes are exactly
`(time, edge-direction)`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspatial : e.2 ≠ (0 : PeriodicHypercubicAxis)) :
    PeriodicHypercubicEvenPlaquette H :=
  (e.1, ⟨((0 : PeriodicHypercubicAxis), e.2), by
    change 0 < e.2.val
    apply Nat.pos_of_ne_zero
    intro hval
    apply hspatial
    apply Fin.ext
    simpa using hval⟩)

@[simp]
theorem periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_firstAxis
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspatial : e.2 ≠ (0 : PeriodicHypercubicAxis)) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion H e hspatial) = 0 := by
  rfl

@[simp]
theorem periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_secondAxis
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspatial : e.2 ≠ (0 : PeriodicHypercubicAxis)) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion H e hspatial) = e.2 := by
  rfl

/-- A spatial edge based on the primary fixed slice determines a
positive-boundary temporal plaquette. -/
theorem periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_positiveBoundary
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspatial : e.2 ≠ (0 : PeriodicHypercubicAxis))
    (hprimary : (e.1 0).val = 0) :
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
      (periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion H e hspatial) := by
  constructor
  · unfold periodicHypercubicEvenPlaquetteHasTimeDirection
    exact Or.inl rfl
  · exact Or.inl hprimary

/-- The relative-kernel boundary leg of the primary-side temporal companion is
exactly the original physical positive edge value.  The backward step `3`
contributes `A(e)⁻¹`, and the boundary-leg definition inverts it once more. -/
theorem periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_boundaryLeg_eq
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspatial : e.2 ≠ (0 : PeriodicHypercubicAxis))
    (hprimary : (e.1 0).val = 0) :
    periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg A
        (periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion H e hspatial) =
      A e := by
  simp [periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg,
    periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion,
    periodicHypercubicStepValue, periodicHypercubicPlaquetteSecondAxis,
    hprimary]

/-- In boundary-fibered coordinates, the companion boundary leg is literally
the selected shared-boundary coordinate. -/
theorem periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_fiberedBoundaryLeg_eq
    {H N : ℕ}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (e : PeriodicHypercubicEvenEdge H)
    (hspatial : e.2 ≠ (0 : PeriodicHypercubicAxis))
    (hprimary : (e.1 0).val = 0)
    (hfixed : periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed) :
    periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b
        (periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion H e hspatial) =
      b ⟨e, hfixed⟩ := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg
  rw [periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_boundaryLeg_eq
    _ e hspatial hprimary]
  exact (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
    b (fun _ => 1) (fun _ => 1) ⟨e, hfixed⟩

/-- Every physical edge of the canonical primary spatial plaquette is spatial. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero
    (H : ℕ) (k : Fin 4) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).2 ≠
      (0 : PeriodicHypercubicAxis) := by
  fin_cases k <;> simp

/-- Every physical edge of the canonical primary spatial plaquette is based on
the primary fixed time slice. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero
    (H : ℕ) (k : Fin 4) :
    ((periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1 0).val = 0 := by
  fin_cases k <;>
    simp [periodicHypercubicEvenPrimarySpatialPlaquetteEdge,
      periodicHypercubicEvenPrimarySpatialPlaquette,
      periodicHypercubicShift_apply]

/-- The four canonical positive-side temporal companions, one for each physical
edge of the primary spatial plaquette. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion
    (H : ℕ) (k : Fin 4) :
    PeriodicHypercubicEvenPlaquette H :=
  periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion H
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k)
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H k)

/-- Each canonical companion belongs to the positive-boundary temporal sector. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_positiveBoundary
    (H : ℕ) (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) := by
  exact periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_positiveBoundary
    H (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k)

/-- The fibered boundary leg of the `k`-th temporal companion is exactly the
`k`-th actual shared-boundary edge coordinate of the primary spatial
plaquette. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq
    {H N : ℕ}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) =
      b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k) := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion,
    periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding] using
    periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion_fiberedBoundaryLeg_eq
      b (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_side_fixed H k)

/-- Exact local kernel formula for the temporal companion of each primary
spatial plaquette edge.  The shared-boundary argument of the relative trace
kernel is now literally the corresponding physical boundary edge variable. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_normalizedTrace_boundaryFibered_eq_relativeKernel
    {H N : ℕ}
    (hH : 0 < H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (k : Fin 4) :
    normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) =
      specialUnitaryNormalizedTraceRelativeKernel N
        (b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_boundaryFibered_eq_relativeKernel
    hH b x y
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_positiveBoundary H k)]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq]

end

end MathlibAnalytic
end MGAP4D