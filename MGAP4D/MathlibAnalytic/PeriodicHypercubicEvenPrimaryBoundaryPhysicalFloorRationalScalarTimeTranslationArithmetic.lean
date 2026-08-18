import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathTimeTranslationCoherence
import Mathlib.Tactic

/-!
# Floor arithmetic for rational-time translation of the primary scalar path

The intrinsic scalar path carries an exact additive action of rational time, but the finite Wilson
readout uses the non-additive selector

`physicalTemporalFloorStep a t n = floor (t / a n)`.

This file isolates the exact arithmetic obstruction before any measure-level stationarity claim.
For arbitrary real times `s,t`, the translated floor step differs from the sum of the two floor
steps by at most one lattice unit.  When the second time is exactly lattice-aligned, Mathlib's
`Int.floor_add_intCast` removes the carry and gives exact integer translation.

The alignment predicate is only a finite-scale receipt.  No rational-time stationarity of the
finite or continuum scalar law, OS contraction, null-space preservation, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The physical floor selector is superadditive up to the usual floor convention. -/
theorem physicalTemporalFloorStep_add_lower
    (latticeSpacing : ℕ → ℝ)
    (s t : ℝ) (n : ℕ) :
    physicalTemporalFloorStep latticeSpacing s n +
        physicalTemporalFloorStep latticeSpacing t n ≤
      physicalTemporalFloorStep latticeSpacing (s + t) n := by
  unfold physicalTemporalFloorStep
  rw [add_div]
  exact Int.le_floor_add _ _

/-- The failure of additivity of the physical floor selector is at most one lattice step. -/
theorem physicalTemporalFloorStep_add_upper
    (latticeSpacing : ℕ → ℝ)
    (s t : ℝ) (n : ℕ) :
    physicalTemporalFloorStep latticeSpacing (s + t) n ≤
      physicalTemporalFloorStep latticeSpacing s n +
        physicalTemporalFloorStep latticeSpacing t n + 1 := by
  unfold physicalTemporalFloorStep
  rw [add_div]
  have h :=
    Int.le_floor_add_floor
      (s / latticeSpacing n) (t / latticeSpacing n)
  omega

/-- Hence the floor selector has exactly two possibilities under addition: no carry or one carry. -/
theorem physicalTemporalFloorStep_add_eq_or_eq_add_one
    (latticeSpacing : ℕ → ℝ)
    (s t : ℝ) (n : ℕ) :
    physicalTemporalFloorStep latticeSpacing (s + t) n =
        physicalTemporalFloorStep latticeSpacing s n +
          physicalTemporalFloorStep latticeSpacing t n ∨
      physicalTemporalFloorStep latticeSpacing (s + t) n =
        physicalTemporalFloorStep latticeSpacing s n +
          physicalTemporalFloorStep latticeSpacing t n + 1 := by
  have hlow := physicalTemporalFloorStep_add_lower latticeSpacing s t n
  have hupp := physicalTemporalFloorStep_add_upper latticeSpacing s t n
  omega

/-- Difference form of the same carry statement. -/
theorem physicalTemporalFloorStep_add_defect_zero_or_one
    (latticeSpacing : ℕ → ℝ)
    (s t : ℝ) (n : ℕ) :
    physicalTemporalFloorStep latticeSpacing (s + t) n -
          (physicalTemporalFloorStep latticeSpacing s n +
            physicalTemporalFloorStep latticeSpacing t n) = 0 ∨
      physicalTemporalFloorStep latticeSpacing (s + t) n -
          (physicalTemporalFloorStep latticeSpacing s n +
            physicalTemporalFloorStep latticeSpacing t n) = 1 := by
  rcases physicalTemporalFloorStep_add_eq_or_eq_add_one latticeSpacing s t n with h | h
  · left
    omega
  · right
    omega

/-- Finite-scale receipt saying that a rational physical time is exactly an integer number of
current lattice spacings.  It is deliberately stronger than merely selecting the same floor step. -/
def PhysicalTemporalFloorRationalTimeAligned
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) (t : ℚ) (k : ℤ) : Prop :=
  (t : ℝ) / latticeSpacing n = (k : ℝ)

@[simp]
theorem physicalTemporalFloorRationalTimeAligned_zero
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    PhysicalTemporalFloorRationalTimeAligned latticeSpacing n 0 0 := by
  simp [PhysicalTemporalFloorRationalTimeAligned]

/-- Exact lattice alignment is additive at a fixed finite scale. -/
theorem PhysicalTemporalFloorRationalTimeAligned.add
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    {s t : ℚ} {k l : ℤ}
    (hs : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n s k)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t l) :
    PhysicalTemporalFloorRationalTimeAligned latticeSpacing n (s + t) (k + l) := by
  unfold PhysicalTemporalFloorRationalTimeAligned at hs ht ⊢
  rw [Rat.cast_add, add_div, hs, ht, Int.cast_add]

/-- If the second real time is exactly `k` lattice spacings, the floor selector translates by
exactly the integer `k`; the possible carry disappears. -/
theorem physicalTemporalFloorStep_add_aligned
    (latticeSpacing : ℕ → ℝ)
    (s t : ℝ) (n : ℕ) (k : ℤ)
    (hk : t / latticeSpacing n = (k : ℝ)) :
    physicalTemporalFloorStep latticeSpacing (s + t) n =
      physicalTemporalFloorStep latticeSpacing s n + k := by
  unfold physicalTemporalFloorStep
  rw [add_div, hk, Int.floor_add_intCast]

/-- Rational-time form of the universal zero-or-one floor carry. -/
theorem physicalTemporalFloorStep_rational_add_eq_or_eq_add_one
    (latticeSpacing : ℕ → ℝ)
    (q t : ℚ) (n : ℕ) :
    physicalTemporalFloorStep latticeSpacing (((q + t : ℚ) : ℝ)) n =
        physicalTemporalFloorStep latticeSpacing (q : ℝ) n +
          physicalTemporalFloorStep latticeSpacing (t : ℝ) n ∨
      physicalTemporalFloorStep latticeSpacing (((q + t : ℚ) : ℝ)) n =
        physicalTemporalFloorStep latticeSpacing (q : ℝ) n +
          physicalTemporalFloorStep latticeSpacing (t : ℝ) n + 1 := by
  simpa using
    (physicalTemporalFloorStep_add_eq_or_eq_add_one
      latticeSpacing (q : ℝ) (t : ℝ) n)

/-- Under the explicit finite-scale alignment receipt, rational path translation becomes exact
integer translation at the level of the physical floor selector. -/
theorem physicalTemporalFloorStep_rational_add_aligned
    (latticeSpacing : ℕ → ℝ)
    (q t : ℚ) (n : ℕ) (k : ℤ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t k) :
    physicalTemporalFloorStep latticeSpacing (((q + t : ℚ) : ℝ)) n =
      physicalTemporalFloorStep latticeSpacing (q : ℝ) n + k := by
  unfold PhysicalTemporalFloorRationalTimeAligned at ht
  simpa using
    (physicalTemporalFloorStep_add_aligned
      latticeSpacing (q : ℝ) (t : ℝ) n k ht)

end

end MathlibAnalytic
end MGAP4D
