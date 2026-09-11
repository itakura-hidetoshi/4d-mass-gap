import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialCrossingGeometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Purely spatial plaquettes belonging to the strict positive interior of the
reflection half-cylinder.  These are precisely the spatial plaquettes on the
interior time slices `1, ..., H`. -/
def periodicHypercubicEvenPositiveHalfSpatialPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenStrictPositivePlaquette p ∧
    ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p

/-- Predicate selecting the time-space plaquettes of the complete positive
half-cylinder.  This combines strict-positive temporal plaquettes with the two
temporal layers adjacent to the reflection-fixed endpoints from the positive
side.  The `Sector` name distinguishes this predicate from the already-existing
explicit slab plaquette embedding. -/
def periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  (periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
      periodicHypercubicEvenStrictPositivePlaquette p) ∨
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p

/-- A purely spatial plaquette belongs to the complete positive half-cylinder
exactly when its base residue is one of the interior slice times `1, ..., H`. -/
theorem periodicHypercubicEvenPositiveHalfSpatialPlaquette_iff_baseTime_val
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPositiveHalfSpatialPlaquette p ↔
      ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        1 ≤ (p.1 0).val ∧ (p.1 0).val ≤ H := by
  unfold periodicHypercubicEvenPositiveHalfSpatialPlaquette
  constructor
  · rintro ⟨hpos, htime⟩
    have hbase :=
      (periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
        p htime).1 hpos
    change periodicHypercubicEvenStrictPositiveTime H (p.1 0) at hbase
    exact ⟨htime, (periodicHypercubicEvenStrictPositiveTime_iff_val H (p.1 0)).1 hbase⟩
  · rintro ⟨htime, hval⟩
    refine ⟨?_, htime⟩
    apply
      (periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
        p htime).2
    change periodicHypercubicEvenStrictPositiveTime H (p.1 0)
    exact (periodicHypercubicEvenStrictPositiveTime_iff_val H (p.1 0)).2 hval

/-- A temporal plaquette belongs to the complete positive half-cylinder exactly
when its base residue is one of the `H+1` slab times `0, ..., H`.  In
particular, the first and last slabs are supplied by the positive-boundary
temporal sector, while the intermediate slabs are strict-positive plaquettes. -/
theorem periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette_iff_baseTime_val_le
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette p ↔
      periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        (p.1 0).val ≤ H := by
  unfold periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette
  constructor
  · rintro (⟨htime, hpos⟩ | hboundary)
    · have hadj :=
        (periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
          p htime).1 hpos
      have hbase :=
        (periodicHypercubicEvenStrictPositiveTime_iff_val H (p.1 0)).1 hadj.1
      exact ⟨htime, hbase.2⟩
    · rcases hboundary with ⟨htime, hzero | hlast⟩
      · exact ⟨htime, by omega⟩
      · exact ⟨htime, by omega⟩
  · rintro ⟨htime, hle⟩
    by_cases hzero : (p.1 0).val = 0
    · exact Or.inr ⟨htime, Or.inl hzero⟩
    · by_cases hlast : (p.1 0).val = H
      · exact Or.inr ⟨htime, Or.inr hlast⟩
      · left
        refine ⟨htime, ?_⟩
        apply
          (periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
            p htime).2
        have hbase : periodicHypercubicEvenStrictPositiveTime H (p.1 0) := by
          rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
          omega
        have hnowrap :
            (p.1 0).val + 1 < PeriodicHypercubicEvenSideLength H := by
          simp only [PeriodicHypercubicEvenSideLength]
          omega
        have hnextVal : ((p.1 0) + 1).val = (p.1 0).val + 1 :=
          periodicHypercubicEven_val_add_one_of_lt H (p.1 0) hnowrap
        have hnext : periodicHypercubicEvenStrictPositiveTime H ((p.1 0) + 1) := by
          rw [periodicHypercubicEvenStrictPositiveTime_iff_val, hnextVal]
          omega
        exact ⟨hbase, hnext⟩

/-- The spatial and temporal positive-half sectors are disjoint. -/
theorem periodicHypercubicEvenPositiveHalfSpatialPlaquette_not_temporalSector
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (hspatial : periodicHypercubicEvenPositiveHalfSpatialPlaquette p) :
    ¬ periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette p := by
  intro htemporal
  have hs :=
    (periodicHypercubicEvenPositiveHalfSpatialPlaquette_iff_baseTime_val p).1 hspatial
  have ht :=
    (periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette_iff_baseTime_val_le p).1
      htemporal
  exact hs.1 ht.1

/-- The completed positive OS plaquette sector is exactly the disjoint union of
its interior spatial slices and all `H+1` temporal slab layers.  This is the
set-theoretic geometry needed before reindexing the Wilson action into the
path-action normal form. -/
theorem periodicHypercubicEvenStrictPositive_or_positiveBoundaryTemporal_iff_positiveHalfSpatial_or_temporalSector
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenStrictPositivePlaquette p ∨
        periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p ↔
      periodicHypercubicEvenPositiveHalfSpatialPlaquette p ∨
        periodicHypercubicEvenPositiveHalfTemporalSectorPlaquette p := by
  constructor
  · intro h
    rcases h with hpos | hboundary
    · by_cases htime : periodicHypercubicEvenPlaquetteHasTimeDirection p
      · exact Or.inr (Or.inl ⟨htime, hpos⟩)
      · exact Or.inl ⟨hpos, htime⟩
    · exact Or.inr (Or.inr hboundary)
  · intro h
    rcases h with hspatial | htemporal
    · exact Or.inl hspatial.1
    · rcases htemporal with hstrict | hboundary
      · exact Or.inl hstrict.2
      · exact Or.inr hboundary

end

end MathlibAnalytic
end MGAP4D
