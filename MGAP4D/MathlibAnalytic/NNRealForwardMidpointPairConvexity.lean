import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic

/-!
# Symmetrizing forward midpoint inequalities on `NNReal`

A forward midpoint inequality parameterized by a base point `a` and an
increment `d ≥ 0` already contains the midpoint inequality for an arbitrary
pair of nonnegative half-times.  The only input is total order on `NNReal`:
order the two half-times and write the larger as the smaller plus a truncated
subtraction.

This is a purely order/algebraic bridge.  It is kept independent of the
Yang--Mills and OS-semigroup layers so that the physical theorem can be a direct
instantiation.
-/

namespace MGAP4D

/-- A forward midpoint inequality on `NNReal` symmetrizes to every pair.

If
`2 f ((a+a)+d) ≤ f (a+a) + f ((a+d)+(a+d))`
for every nonnegative increment `d`, then
`2 f (a+b) ≤ f (a+a) + f (b+b)`
for arbitrary nonnegative half-times `a,b`. -/
theorem nnreal_two_mul_add_le_add_doubled_of_forward_midpoint
    (f : NNReal → ℝ)
    (hforward : ∀ a d : NNReal,
      2 * f ((a + a) + d) ≤
        f (a + a) + f ((a + d) + (a + d)))
    (a b : NNReal) :
    2 * f (a + b) ≤ f (a + a) + f (b + b) := by
  rcases le_total a b with hab | hba
  · let d : NNReal := b - a
    have had : a + d = b := by
      dsimp [d]
      simpa [add_comm] using (tsub_add_cancel_of_le hab)
    have hmid : (a + a) + d = a + b := by
      calc
        (a + a) + d = a + (a + d) := by ac_rfl
        _ = a + b := by rw [had]
    have h := hforward a d
    rw [hmid, had] at h
    exact h
  · let d : NNReal := a - b
    have hbd : b + d = a := by
      dsimp [d]
      simpa [add_comm] using (tsub_add_cancel_of_le hba)
    have hmid : (b + b) + d = a + b := by
      calc
        (b + b) + d = b + (b + d) := by ac_rfl
        _ = b + a := by rw [hbd]
        _ = a + b := by ac_rfl
    have h := hforward b d
    rw [hmid, hbd] at h
    simpa [add_comm] using h

end MGAP4D
