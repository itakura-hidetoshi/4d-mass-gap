import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Partition.Finpartition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Möbius coefficient of a set partition with `k` blocks.

For `k > 0` this is the standard moment-cumulant coefficient
`(k - 1)! * (-1)^(k - 1)`.  We set the coefficient at `k = 0` to zero so that
the empty-index cumulant has the conventional value zero rather than inheriting
an artefact from truncated subtraction on `ℕ`. -/
def finiteCumulantMobiusCoefficient {R : Type*} [CommRing R] (k : ℕ) : R :=
  if k = 0 then 0
  else (Nat.factorial (k - 1) : R) * (-1 : R) ^ (k - 1)

@[simp]
theorem finiteCumulantMobiusCoefficient_zero {R : Type*} [CommRing R] :
    finiteCumulantMobiusCoefficient (R := R) 0 = 0 := by
  simp [finiteCumulantMobiusCoefficient]

theorem finiteCumulantMobiusCoefficient_of_pos
    {R : Type*} [CommRing R] {k : ℕ} (hk : 0 < k) :
    finiteCumulantMobiusCoefficient (R := R) k =
      (Nat.factorial (k - 1) : R) * (-1 : R) ^ (k - 1) := by
  simp [finiteCumulantMobiusCoefficient, Nat.ne_of_gt hk]

/-- The finite cumulant associated with a family of block moments.

A `Finpartition J` is exactly a finite partition of the finite index set `J`,
so this is the standard moment-cumulant formula

`κ_J = ∑_π (|π|-1)! (-1)^(|π|-1) ∏_{B∈π} M_B`.

The definition is algebraic over an arbitrary commutative ring. -/
def finiteCumulant
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) (moment : Finset α → R) : R :=
  ∑ P : Finpartition J,
    finiteCumulantMobiusCoefficient (R := R) P.parts.card *
      ∏ B ∈ P.parts, moment B

/-- Cumulants are functorial under pointwise equality of all block moments.
This is the only combinatorial transport needed for translation invariance:
once every finite block moment is unchanged, the finite partition sum is
unchanged term by term. -/
theorem finiteCumulant_congr
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) {moment moment' : Finset α → R}
    (h : ∀ B, moment' B = moment B) :
    finiteCumulant J moment' = finiteCumulant J moment := by
  simp [finiteCumulant, h]

end

end MathlibAnalytic
end MGAP4D
