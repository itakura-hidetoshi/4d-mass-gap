import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The real-valued cubic shell profile supplied by three spatial link
orientations and the signed displacement cube [-r,r]^3. -/
def cubicSpatialShellMajorant (r : Nat) : Real :=
  3 * (2 * (r : Real) + 1) ^ 3

/-- The cubic spatial shell majorant is nonnegative. -/
theorem cubicSpatialShellMajorant_nonneg
    (r : Nat) :
    0 <= cubicSpatialShellMajorant r := by
  unfold cubicSpatialShellMajorant
  positivity

/-- Any cubic spatial shell profile is summable against geometric decay as
soon as the geometric ratio has norm strictly below one. No extra condition
such as 18*q<1 is required. -/
theorem summable_cubicSpatialShellMajorant_mul_geometric
    (C q : Real)
    (hq : ‖q‖ < 1) :
    Summable (fun r : Nat =>
      cubicSpatialShellMajorant r * (C * q ^ r)) := by
  have h0 :
      Summable (fun n : Nat => q ^ n : Nat -> Real) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 0 hq)
  have h1 :
      Summable (fun n : Nat => (n : Real) * q ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 1 hq)
  have h2 :
      Summable (fun n : Nat => (n : Real) ^ 2 * q ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 2 hq)
  have h3 :
      Summable (fun n : Nat => (n : Real) ^ 3 * q ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 3 hq)
  have hExpanded :
      Summable (fun n : Nat =>
        (24 * C) * ((n : Real) ^ 3 * q ^ n) +
        (36 * C) * ((n : Real) ^ 2 * q ^ n) +
        (18 * C) * ((n : Real) * q ^ n) +
        (3 * C) * q ^ n) :=
    (((h3.mul_left (24 * C)).add
      (h2.mul_left (36 * C))).add
      (h1.mul_left (18 * C))).add
      (h0.mul_left (3 * C))
  apply hExpanded.congr
  intro n
  unfold cubicSpatialShellMajorant
  ring

/-- Convenient positive-ratio version used by the terminal spatial-decay
certificate. -/
theorem summable_cubicSpatialShellMajorant_mul_geometric_of_nonneg_lt_one
    (C q : Real)
    (hqNonneg : 0 <= q)
    (hqLtOne : q < 1) :
    Summable (fun r : Nat =>
      cubicSpatialShellMajorant r * (C * q ^ r)) := by
  apply summable_cubicSpatialShellMajorant_mul_geometric C q
  rw [Real.norm_eq_abs, abs_of_nonneg hqNonneg]
  exact hqLtOne

end

end MathlibAnalytic
end MGAP4D
