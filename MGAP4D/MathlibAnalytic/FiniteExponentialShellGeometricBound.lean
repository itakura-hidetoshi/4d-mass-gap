import MGAP4D.MathlibAnalytic.FiniteDistanceShellGeometricSum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteDistanceShellGeometricSum

/-- Elementary finite geometric-sum identity, proved directly for later shell
estimates without relying on an infinite-series API. -/
theorem one_sub_mul_sum_range_pow
    (q : Real) (n : Nat) :
    (1 - q) * Finset.sum (Finset.range n) (fun m => q ^ m) =
      1 - q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- Every finite partial geometric sum is bounded by the full geometric mass
`1 / (1 - q)` when `0 <= q < 1`. -/
theorem sum_range_pow_le_one_div_one_sub
    (q : Real) (hqNonneg : 0 <= q) (hqLtOne : q < 1) (n : Nat) :
    Finset.sum (Finset.range n) (fun m => q ^ m) <=
      1 / (1 - q) := by
  have hDenomPos : 0 < 1 - q := sub_pos.mpr hqLtOne
  apply (le_div_iff₀ hDenomPos).2
  calc
    Finset.sum (Finset.range n) (fun m => q ^ m) * (1 - q) =
        (1 - q) * Finset.sum (Finset.range n) (fun m => q ^ m) := by
      ring
    _ = 1 - q ^ n := one_sub_mul_sum_range_pow q n
    _ <= 1 := sub_le_self _ (pow_nonneg hqNonneg n)

variable {P : Type*} [Fintype P]

/-- Exponential shell-cardinality growth whose product with the covariance
decay ratio remains strictly below one. -/
structure FiniteExponentialShellControl (P : Type*) [Fintype P] where
  distance : P -> Nat
  radius : Nat
  ratio : Real
  shellPrefactor : Real
  shellGrowth : Real
  ratio_nonneg : 0 <= ratio
  ratio_lt_one : ratio < 1
  shellPrefactor_nonneg : 0 <= shellPrefactor
  shellGrowth_nonneg : 0 <= shellGrowth
  growth_mul_ratio_lt_one : shellGrowth * ratio < 1
  distance_lt_radius : forall p : P, distance p < radius
  shell_card_real_le :
    forall m : Nat,
      ((Finset.univ.filter fun p : P => distance p = m).card : Real) <=
        shellPrefactor * shellGrowth ^ m

namespace FiniteExponentialShellControl

/-- Exponential shell growth is summable against a faster exponential decay,
with explicit mass `shellPrefactor / (1 - shellGrowth * ratio)`. -/
noncomputable def toFiniteGeometricShellControl
    (C : FiniteExponentialShellControl P) :
    FiniteGeometricShellControl P :=
  { distance := C.distance
    radius := C.radius
    shellCardBound := fun m =>
      (Finset.univ.filter fun p : P => C.distance p = m).card
    shellMass := C.shellPrefactor / (1 - C.shellGrowth * C.ratio)
    ratio := C.ratio
    shellMass_nonneg := by
      exact div_nonneg C.shellPrefactor_nonneg
        (sub_nonneg.mpr (le_of_lt C.growth_mul_ratio_lt_one))
    ratio_nonneg := C.ratio_nonneg
    ratio_lt_one := C.ratio_lt_one
    distance_lt_radius := C.distance_lt_radius
    shell_card_le := by
      intro m
      exact le_rfl
    weighted_shell_sum_le := by
      have hProductNonneg : 0 <= C.shellGrowth * C.ratio :=
        mul_nonneg C.shellGrowth_nonneg C.ratio_nonneg
      calc
        Finset.sum (Finset.range C.radius) (fun m =>
            (((Finset.univ.filter fun p : P => C.distance p = m).card : Nat) : Real) *
              C.ratio ^ m) <=
          Finset.sum (Finset.range C.radius) (fun m =>
            C.shellPrefactor * (C.shellGrowth * C.ratio) ^ m) := by
              apply Finset.sum_le_sum
              intro m _hm
              calc
                (((Finset.univ.filter fun p : P => C.distance p = m).card : Nat) : Real) *
                    C.ratio ^ m <=
                  (C.shellPrefactor * C.shellGrowth ^ m) * C.ratio ^ m :=
                    mul_le_mul_of_nonneg_right
                      (C.shell_card_real_le m)
                      (pow_nonneg C.ratio_nonneg m)
                _ = C.shellPrefactor * (C.shellGrowth * C.ratio) ^ m := by
                  rw [mul_pow]
                  ring
        _ = C.shellPrefactor *
            Finset.sum (Finset.range C.radius) (fun m =>
              (C.shellGrowth * C.ratio) ^ m) := by
              rw [Finset.mul_sum]
        _ <= C.shellPrefactor *
            (1 / (1 - C.shellGrowth * C.ratio)) :=
              mul_le_mul_of_nonneg_left
                (sum_range_pow_le_one_div_one_sub
                  (C.shellGrowth * C.ratio)
                  hProductNonneg C.growth_mul_ratio_lt_one C.radius)
                C.shellPrefactor_nonneg
        _ = C.shellPrefactor / (1 - C.shellGrowth * C.ratio) := by
          simp [div_eq_mul_inv] }

/-- Explicit exponential shell control bounds the total geometric weight. -/
theorem sum_pow_distance_le_explicit
    (C : FiniteExponentialShellControl P) :
    (Finset.univ.sum fun p : P => C.ratio ^ C.distance p) <=
      C.shellPrefactor / (1 - C.shellGrowth * C.ratio) :=
  C.toFiniteGeometricShellControl.sum_pow_distance_le

end FiniteExponentialShellControl

end FiniteDistanceShellGeometricSum

end

end MathlibAnalytic
end MGAP4D
