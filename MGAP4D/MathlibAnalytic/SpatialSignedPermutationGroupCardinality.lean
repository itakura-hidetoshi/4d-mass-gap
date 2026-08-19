import MGAP4D.MathlibAnalytic.SpatialSignedPermutationGroup
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Cardinality of the abstract three-dimensional signed permutation group

The abstract spatial signed-permutation group is the semidirect product

`(Fin 3 → ℤˣ) ⋊ S₃`.

The integer unit group has exactly two elements, so the sign-function group has `2^3 = 8`
elements.  The permutation group of three axes has `3! = 6` elements.  Since a semidirect product
has the product carrier, the abstract signed-coordinate group therefore has exactly

`8 * 6 = 48`

elements.

This is the finite-order theorem for the abstract group.  Generation by the distinguished three
generators, comparison with the concrete configuration action, cubic representation labels,
continuum spin, and spectral statements remain separate downstream obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- There are exactly `2^3 = 8` sign assignments on the three spatial axes. -/
theorem spatialAxisSign_card :
    Fintype.card SpatialAxisSign = 8 := by
  classical
  change Fintype.card (Fin 3 → ℤˣ) = 8
  rw [Fintype.card_fun, Fintype.card_units_int]
  norm_num

/-- The permutation group of the three abstract spatial coordinate axes has `3! = 6` elements. -/
theorem spatialAxisPermutation_card :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm]
  norm_num

/-- The abstract three-dimensional signed permutation group has exactly `48` elements. -/
theorem spatialSignedPermutationGroup_card :
    Fintype.card SpatialSignedPermutationGroup = 48 := by
  change Fintype.card (SpatialAxisSign × Equiv.Perm (Fin 3)) = 48
  rw [Fintype.card_prod, spatialAxisSign_card, spatialAxisPermutation_card]
  norm_num

/-- Audit-visible finite-order formulation using `Nat.card`. -/
theorem spatialSignedPermutationGroup_natCard :
    Nat.card SpatialSignedPermutationGroup = 48 := by
  rw [Nat.card_eq_fintype_card, spatialSignedPermutationGroup_card]

end

end MathlibAnalytic
end MGAP4D
