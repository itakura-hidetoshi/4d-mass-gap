import MGAP4D.MathlibAnalytic.SpatialSignedPermutationGroup
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Cardinality of the abstract three-dimensional signed permutation group

The abstract spatial signed-permutation group is the semidirect product

`(Fin 3 → ℤˣ) ⋊ S₃`.

The integer unit group has exactly two elements, so the sign-function group has `2^3 = 8`
elements.  The permutation group of three axes has `3! = 6` elements.  Since a semidirect product
has a canonical equivalence with its product carrier, the abstract signed-coordinate group therefore
has exactly

`8 * 6 = 48`

elements.

This file keeps the proof compatible with the repository-pinned mathlib version: the pinned tree
already proves `ℤˣ = {1, -1}` but does not yet provide the later standalone integer-units `Fintype`
module.  We therefore install the finite instances locally from the canonical existing theorem and
from `SemidirectProduct.equivProd`.

This is the finite-order theorem for the abstract group.  Generation by the distinguished three
generators, comparison with the concrete configuration action, cubic representation labels,
continuum spin, and spectral statements remain separate downstream obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Repository-pin-compatible finite enumeration of the two integer units. -/
local instance spatialIntegerUnitsFintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun u => by
    rcases Int.units_eq_one_or u with h | h
    · simp [h]
    · simp [h]⟩

/-- The repository-pinned integer unit type has exactly two elements. -/
theorem spatialIntegerUnits_card :
    Fintype.card ℤˣ = 2 := by
  native_decide

/-- Install finiteness of the semidirect product through its canonical product equivalence. -/
local instance spatialSignedPermutationGroupFintype :
    Fintype SpatialSignedPermutationGroup :=
  Fintype.ofEquiv
    (SpatialAxisSign × Equiv.Perm (Fin 3))
    (SemidirectProduct.equivProd (φ := spatialAxisPermutationSignAction)).symm

/-- There are exactly `2^3 = 8` sign assignments on the three spatial axes. -/
theorem spatialAxisSign_card :
    Fintype.card SpatialAxisSign = 8 := by
  classical
  change Fintype.card (Fin 3 → ℤˣ) = 8
  rw [Fintype.card_fun, spatialIntegerUnits_card]
  norm_num

/-- The permutation group of the three abstract spatial coordinate axes has `3! = 6` elements. -/
theorem spatialAxisPermutation_card :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm]
  norm_num

/-- The abstract three-dimensional signed permutation group has exactly `48` elements. -/
theorem spatialSignedPermutationGroup_card :
    Fintype.card SpatialSignedPermutationGroup = 48 := by
  calc
    Fintype.card SpatialSignedPermutationGroup =
        Fintype.card (SpatialAxisSign × Equiv.Perm (Fin 3)) :=
      Fintype.card_congr
        (SemidirectProduct.equivProd (φ := spatialAxisPermutationSignAction))
    _ = 48 := by
      rw [Fintype.card_prod, spatialAxisSign_card, spatialAxisPermutation_card]

/-- Audit-visible finite-order formulation using `Nat.card`. -/
theorem spatialSignedPermutationGroup_natCard :
    Nat.card SpatialSignedPermutationGroup = 48 := by
  rw [Nat.card_eq_fintype_card, spatialSignedPermutationGroup_card]

end

end MathlibAnalytic
end MGAP4D
