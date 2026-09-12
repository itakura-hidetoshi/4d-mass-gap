import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveHalfPlaquetteCoordinateEquivalences
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfPathActionNormalForm
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance completedPositiveActionSpatialSectorFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenPositiveHalfSpatialPlaquetteSubtype H) :=
  Fintype.ofFinite _

local instance completedPositiveActionTemporalSectorFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteSubtype H) :=
  Fintype.ofFinite _

/-- Wilson action carried by the purely-spatial strict-positive plaquettes. -/
noncomputable def periodicHypercubicEvenPositiveHalfSpatialWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenPositiveHalfSpatialPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- Wilson action carried by all time-space plaquettes of the complete positive
half-cylinder, including the two positive-side boundary temporal layers. -/
noncomputable def periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- An indicator sum over a finite carrier is the corresponding sum over the
subtype satisfying the predicate. -/
private theorem completedPositiveAction_sum_indicator_eq_subtype
    {ι : Type*} [Fintype ι]
    (P : ι → Prop)
    [Fintype {i // P i}]
    (f : ι → ℝ) :
    (∑ i : ι, propositionIndicator (P i) (f i)) =
      ∑ i : {i // P i}, f i := by
  classical
  calc
    (∑ i : ι, propositionIndicator (P i) (f i)) =
        ∑ i ∈ (Finset.univ.filter P : Finset ι), f i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      simp [propositionIndicator]
    _ = ∑ i : {i // P i}, f i := by
      exact Finset.sum_subtype
        (Finset.univ.filter P) (fun i => by simp) f

/-- A positive-boundary temporal plaquette cannot simultaneously lie wholly in
the strict positive open half. -/
theorem periodicHypercubicEvenStrictPositivePlaquette_not_positiveBoundaryTemporal
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hpos : periodicHypercubicEvenStrictPositivePlaquette p) :
    ¬ periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p := by
  intro hboundary
  have hcross : periodicHypercubicEvenTemporalCrossingPlaquette p :=
    (periodicHypercubicEvenTemporalCrossingPlaquette_iff_positiveBoundary_or_negativeBoundary
      p).2 (Or.inl hboundary)
  exact hcross.1.1 hpos

/-- The completed-positive non-spatial-boundary action splits exactly into the
interior spatial sector and the complete `H+1`-slab temporal sector. -/
theorem periodicHypercubicEvenPositiveWilsonAction_add_positiveBoundaryTemporal_eq_spatial_add_temporalSector
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      periodicHypercubicEvenPositiveHalfSpatialWilsonAction H N A +
        periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenPositiveWilsonAction
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  unfold periodicHypercubicEvenPositiveHalfSpatialWilsonAction
  unfold periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpos : periodicHypercubicEvenStrictPositivePlaquette p
  · have hnotboundary :=
      periodicHypercubicEvenStrictPositivePlaquette_not_positiveBoundaryTemporal p hpos
    by_cases htime : periodicHypercubicEvenPlaquetteHasTimeDirection p
    · simp [propositionIndicator,
        periodicHypercubicEvenPositiveHalfSpatialPlaquette,
        periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette,
        hpos, hnotboundary, htime]
    · simp [propositionIndicator,
        periodicHypercubicEvenPositiveHalfSpatialPlaquette,
        periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette,
        hpos, hnotboundary, htime]
  · by_cases hboundary : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
    · simp [propositionIndicator,
        periodicHypercubicEvenPositiveHalfSpatialPlaquette,
        periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette,
        hpos, hboundary]
    · simp [propositionIndicator,
        periodicHypercubicEvenPositiveHalfSpatialPlaquette,
        periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette,
        hpos, hboundary]

/-- Reindex the strict-positive purely-spatial Wilson action by the `H`
interior time slices and intrinsic spatial-slice plaquettes. -/
theorem periodicHypercubicEvenPositiveHalfSpatialWilsonAction_eq_interiorSliceSum
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveHalfSpatialWilsonAction H N A =
      ∑ k : Fin H,
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
            (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)))) := by
  classical
  let energy := fun p : PeriodicHypercubicEvenPlaquette H =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)
  have hsub :
      periodicHypercubicEvenPositiveHalfSpatialWilsonAction H N A =
        ∑ q : PeriodicHypercubicEvenPositiveHalfSpatialPlaquetteSubtype H,
          energy q.1 := by
    unfold periodicHypercubicEvenPositiveHalfSpatialWilsonAction
    simpa [energy] using
      completedPositiveAction_sum_indicator_eq_subtype
        (fun p : PeriodicHypercubicEvenPlaquette H =>
          periodicHypercubicEvenPositiveHalfSpatialPlaquette p) energy
  rw [hsub]
  have hreindex :=
    (periodicHypercubicEvenPositiveHalfSpatialPlaquetteCoordinateEquiv H).sum_comp
      (fun q : PeriodicHypercubicEvenPositiveHalfSpatialPlaquetteSubtype H =>
        energy q.1)
  rw [← hreindex]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _hk
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  simp [periodicHypercubicEvenPositiveHalfSpatialPlaquetteCoordinateEquiv,
    periodicHypercubicEvenPositiveHalfSpatialPlaquetteFromCoordinates,
    periodicHypercubicEvenSpatialSlicePlaquetteList, energy]
  simp_rw [periodicHypercubicEvenSpatialSlicePlaquetteEnergy_restrictionAtTime_eq]

/-- Reindex all completed-positive temporal Wilson plaquettes by the `H+1`
physical slabs.  The resulting inner sum is literally the unfixed temporal
crossing action used by the path integral. -/
theorem periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction_eq_temporalPathAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction H N A =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
        H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N A) := by
  classical
  let energy := fun p : PeriodicHypercubicEvenPlaquette H =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)
  have hsub :
      periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction H N A =
        ∑ q : PeriodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteSubtype H,
          energy q.1 := by
    unfold periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction
    simpa [energy] using
      completedPositiveAction_sum_indicator_eq_subtype
        (fun p : PeriodicHypercubicEvenPlaquette H =>
          periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette p) energy
  rw [hsub]
  have hreindex :=
    (periodicHypercubicEvenPositiveHalfTemporalPlaquetteCoordinateEquiv H).sum_comp
      (fun q : PeriodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteSubtype H =>
        energy q.1)
  rw [← hreindex]
  rw [Fintype.sum_prod_type]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
  apply Finset.sum_congr rfl
  intro i _hi
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction
  simp [periodicHypercubicEvenPositiveHalfTemporalPlaquetteCoordinateEquiv,
    periodicHypercubicEvenPositiveHalfTemporalSectorPlaquetteFromCoordinates,
    periodicHypercubicEvenSpatialSliceLinkList, energy]
  simp_rw [periodicHypercubicEvenPositiveHalfTemporalPlaquette_energy_eq_unfixed]

/-- Global completed-positive bulk/temporal action in actual four-dimensional
coordinates, rewritten exactly as the interior spatial-slice action plus the
unfixed temporal path action. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonAction_eq_interiorSpatial_add_temporalPath
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      (∑ k : Fin H,
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime H N A
            (((k.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))))) +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
          H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
            H N A)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
            H N A) := by
  rw [periodicHypercubicEvenPositiveWilsonAction_add_positiveBoundaryTemporal_eq_spatial_add_temporalSector]
  rw [periodicHypercubicEvenPositiveHalfSpatialWilsonAction_eq_interiorSliceSum]
  rw [periodicHypercubicEvenPositiveHalfTemporalSectorWilsonAction_eq_temporalPathAction]

end

end MathlibAnalytic
end MGAP4D
