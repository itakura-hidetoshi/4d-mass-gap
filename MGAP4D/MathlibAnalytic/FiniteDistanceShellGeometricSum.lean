import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteDistanceShellGeometricSum

variable {P : Type*} [Fintype P]

/-- A finite geometric weight sum can be regrouped exactly by the level sets of
an integer-valued distance bounded by a finite radius. -/
theorem sum_pow_distance_eq_shell_sum
    (distance : P -> Nat) (radius : Nat)
    (hDistance : forall p : P, distance p < radius)
    (ratio : Real) :
    (Finset.univ.sum fun p : P => ratio ^ distance p) =
      Finset.sum (Finset.range radius) fun m =>
        ((Finset.univ.filter fun p : P => distance p = m).card : Real) *
          ratio ^ m := by
  classical
  calc
    (Finset.univ.sum fun p : P => ratio ^ distance p) =
        Finset.univ.sum fun p : P =>
          Finset.sum (Finset.range radius) fun m =>
            if distance p = m then ratio ^ m else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      symm
      rw [Finset.sum_eq_single (distance p)]
      · simp
      · intro m hm hNe
        simp [Ne.symm hNe]
      · intro hNotMem
        exact (hNotMem (Finset.mem_range.mpr (hDistance p))).elim
    _ = Finset.sum (Finset.range radius) fun m =>
        Finset.univ.sum fun p : P =>
          if distance p = m then ratio ^ m else 0 := by
      rw [Finset.sum_comm]
    _ = Finset.sum (Finset.range radius) fun m =>
        ((Finset.univ.filter fun p : P => distance p = m).card : Real) *
          ratio ^ m := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [<- Finset.sum_filter]
      simp

/-- Finite shell-cardinality data controlling the total geometric weight of an
integer-valued distance. -/
structure FiniteGeometricShellControl (P : Type*) [Fintype P] where
  distance : P -> Nat
  radius : Nat
  shellCardBound : Nat -> Nat
  shellMass : Real
  ratio : Real
  shellMass_nonneg : 0 <= shellMass
  ratio_nonneg : 0 <= ratio
  ratio_lt_one : ratio < 1
  distance_lt_radius : forall p : P, distance p < radius
  shell_card_le :
    forall m : Nat,
      (Finset.univ.filter fun p : P => distance p = m).card <=
        shellCardBound m
  weighted_shell_sum_le :
    Finset.sum (Finset.range radius) (fun m =>
      (shellCardBound m : Real) * ratio ^ m) <= shellMass

namespace FiniteGeometricShellControl

/-- Shell-cardinality control implies a uniform bound on the finite geometric
weight sum. -/
theorem sum_pow_distance_le
    (C : FiniteGeometricShellControl P) :
    (Finset.univ.sum fun p : P => C.ratio ^ C.distance p) <= C.shellMass := by
  rw [sum_pow_distance_eq_shell_sum
    C.distance C.radius C.distance_lt_radius C.ratio]
  calc
    Finset.sum (Finset.range C.radius) (fun m =>
        ((Finset.univ.filter fun p : P => C.distance p = m).card : Real) *
          C.ratio ^ m) <=
      Finset.sum (Finset.range C.radius) (fun m =>
        (C.shellCardBound m : Real) * C.ratio ^ m) := by
      apply Finset.sum_le_sum
      intro m _hm
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast C.shell_card_le m
      · exact pow_nonneg C.ratio_nonneg _
    _ <= C.shellMass := C.weighted_shell_sum_le

end FiniteGeometricShellControl

end FiniteDistanceShellGeometricSum

end

end MathlibAnalytic
end MGAP4D
