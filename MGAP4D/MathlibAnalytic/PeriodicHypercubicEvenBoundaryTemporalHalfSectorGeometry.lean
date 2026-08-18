import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenHalfSectorBoundaryFiberedDependence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation
import Mathlib.Tactic

/-!
# Temporal translation geometry of the two reflection-fixed slices

The even periodic lattice has two reflection-fixed spatial slices: the primary
slice at residue `0` and the antipodal slice at residue `H + 1`.  For positive
integer translation distances below the half extent these two slices behave
differently:

* translating the primary slice by `k ≤ H` stays in the boundary/positive half;
* translating the antipodal slice by `1 ≤ k ≤ H` enters the negative half.

This distinction is essential for positive-time OS locality.  In particular, a
full `BoundaryConfiguration` contains both fixed slices, so a translated
observable depending on the entire boundary configuration cannot be declared
positive-half local merely from the sign of `k`.

The final theorem below records the constructive half of the geometry needed by
a one-sided primary-boundary readout: changing the negative-half coordinate of
the canonical boundary-fibered assembly cannot change any translated primary
spatial boundary edge while `k ≤ H`.

No reflection-positivity, continuum, scaling, or spectral assumption is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Before wraparound, positive integer temporal edge translation adds exactly
`k` to the canonical source-time residue. -/
theorem periodicHypercubicEvenIntegerTemporalEdgeTranslation_sourceTime_val_of_add_lt
    (H k : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hadd : (e.1 0).val + k < PeriodicHypercubicEvenSideLength H) :
    ((periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e).1 0).val =
      (e.1 0).val + k := by
  have hklt : k < PeriodicHypercubicEvenSideLength H := by
    omega
  have hkval :
      ((k : ZMod (PeriodicHypercubicEvenSideLength H))).val = k :=
    ZMod.val_natCast_of_lt hklt
  change
    (e.1 0 +
      periodicHypercubicIntegerTemporalDisplacement
        (PeriodicHypercubicEvenSideLength H) (k : ℤ) 0).val =
      (e.1 0).val + k
  rw [periodicHypercubicIntegerTemporalDisplacement_time]
  have hkcast :
      (((k : ℤ) : ZMod (PeriodicHypercubicEvenSideLength H))) =
        (k : ZMod (PeriodicHypercubicEvenSideLength H)) := by
    norm_num
  rw [hkcast]
  have hsum :
      (e.1 0).val +
          ((k : ZMod (PeriodicHypercubicEvenSideLength H))).val <
        PeriodicHypercubicEvenSideLength H := by
    simpa [hkval] using hadd
  rw [ZMod.val_add_of_lt hsum, hkval]

/-- A primary fixed-slice spatial edge translated by any `k ≤ H` is never in
the negative edge sector.  The case `k = 0` remains fixed; positive `k` lies in
the selected positive half. -/
theorem periodicHypercubicEvenEdgeSide_integerTemporalTranslate_primary_ne_negative
    (H k : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hprimary : (e.1 0).val = 0)
    (hk : k ≤ H) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e) ≠
      ReflectionEdgeSide.negative := by
  let e' : PeriodicHypercubicEvenEdge H :=
    periodicHypercubicEdgeTranslationEquiv
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicIntegerTemporalDisplacement
        (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e
  have hadd :
      (e.1 0).val + k < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hval : (e'.1 0).val = (e.1 0).val + k := by
    simpa [e'] using
      periodicHypercubicEvenIntegerTemporalEdgeTranslation_sourceTime_val_of_add_lt
        H k e hadd
  have hspace' : e'.2 ≠ 0 := by
    simpa [e', periodicHypercubicEdgeTranslationEquiv] using hspace
  have hle : (e'.1 0).val ≤ H + 1 := by
    rw [hval, hprimary]
    omega
  exact
    periodicHypercubicEvenEdgeSide_spatial_ne_negative_of_val_le_half
      H e' hspace' hle

/-- A spatial edge on the antipodal fixed slice enters the negative sector
after every strictly positive translation `1 ≤ k ≤ H`. -/
theorem periodicHypercubicEvenEdgeSide_integerTemporalTranslate_antipodal_eq_negative
    (H k : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hantipodal : (e.1 0).val = H + 1)
    (hkpos : 1 ≤ k)
    (hk : k ≤ H) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e) =
      ReflectionEdgeSide.negative := by
  let e' : PeriodicHypercubicEvenEdge H :=
    periodicHypercubicEdgeTranslationEquiv
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicIntegerTemporalDisplacement
        (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e
  have hadd :
      (e.1 0).val + k < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hval : (e'.1 0).val = (e.1 0).val + k := by
    simpa [e'] using
      periodicHypercubicEvenIntegerTemporalEdgeTranslation_sourceTime_val_of_add_lt
        H k e hadd
  have hspace' : e'.2 ≠ 0 := by
    simpa [e', periodicHypercubicEdgeTranslationEquiv] using hspace
  have hneg : H + 1 < (e'.1 0).val := by
    rw [hval, hantipodal]
    omega
  exact
    periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
      H e' hspace' hneg

/-- In canonical boundary-fibered coordinates, a translated primary spatial
boundary edge is independent of the negative-half input throughout
`0 ≤ k ≤ H`.

This is the exact pointwise locality receipt needed to build a one-sided
primary-boundary positive-time observable without imposing a new locality
premise. -/
theorem periodicHypercubicEvenBoundaryFiberedAssemble_integerTemporalTranslate_primary_independent_negative
    {H : ℕ} {Value : Type*}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y₁ y₂ :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value)
    (k : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hprimary : (e.1 0).val = 0)
    (hk : k ≤ H) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
        b x y₁
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e) =
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
        b x y₂
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e) := by
  apply
    FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_eq_of_side_ne_negative
      (periodicHypercubicEvenEdgeOrbitPartition H) b x y₁ y₂
  change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e) ≠
    ReflectionEdgeSide.negative
  exact
    periodicHypercubicEvenEdgeSide_integerTemporalTranslate_primary_ne_negative
      H k e hspace hprimary hk

end

end MathlibAnalytic
end MGAP4D
