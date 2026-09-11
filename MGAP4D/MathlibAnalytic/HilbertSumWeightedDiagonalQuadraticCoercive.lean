import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalDenseSymmetric
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace lp

noncomputable section

universe u v

/-- A real maximal weighted diagonal whose weights are uniformly bounded below
by `c` has quadratic form bounded below by `c * ‖x‖²` on its full natural
domain.  This is the coordinate-level coercivity theorem needed to lift a
pointwise spectral energy gap to the whole domain of the logarithmic
Hamiltonian. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_quadratic_lower_bound
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    (w : ι → ℝ)
    (c : ℝ)
    (hLower : ∀ i, c ≤ w i)
    (x : (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain) :
    c * ‖(x : lp G 2)‖ ^ 2 ≤
      inner ℝ
        (realHilbertSumWeightedDiagonalLinearPMap (G := G) w x)
        (x : lp G 2) := by
  let xv : lp G 2 := (x : lp G 2)
  let Ax : lp G 2 := realHilbertSumWeightedDiagonalLinearPMap (G := G) w x
  have hLeft : Summable (fun i => inner ℝ ((c • xv) i) (xv i)) :=
    lp.summable_inner (c • xv) xv
  have hRight : Summable (fun i => inner ℝ (Ax i) (xv i)) :=
    lp.summable_inner Ax xv
  have hPoint : ∀ i, inner ℝ ((c • xv) i) (xv i) ≤ inner ℝ (Ax i) (xv i) := by
    intro i
    change inner ℝ (c • xv i) (xv i) ≤
      inner ℝ (w i • xv i) (xv i)
    rw [real_inner_smul_left, real_inner_smul_left]
    exact mul_le_mul_of_nonneg_right (hLower i) real_inner_self_nonneg
  calc
    c * ‖(x : lp G 2)‖ ^ 2 = inner ℝ (c • xv) xv := by
      simp [xv, real_inner_smul_left, real_inner_self_eq_norm_sq]
    _ = ∑' i, inner ℝ ((c • xv) i) (xv i) := lp.inner_eq_tsum _ _
    _ ≤ ∑' i, inner ℝ (Ax i) (xv i) := hLeft.tsum_le_tsum hPoint hRight
    _ = inner ℝ Ax xv := (lp.inner_eq_tsum _ _).symm
    _ = inner ℝ
        (realHilbertSumWeightedDiagonalLinearPMap (G := G) w x)
        (x : lp G 2) := by rfl

/-- Nonnegative weights give a nonnegative quadratic form on the maximal
weighted domain. -/
theorem realHilbertSumWeightedDiagonalLinearPMap_quadratic_nonneg
    {ι : Type u}
    {G : ι → Type v}
    [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℝ (G i)]
    (w : ι → ℝ)
    (hNonneg : ∀ i, 0 ≤ w i)
    (x : (realHilbertSumWeightedDiagonalLinearPMap (G := G) w).domain) :
    0 ≤ inner ℝ
      (realHilbertSumWeightedDiagonalLinearPMap (G := G) w x)
      (x : lp G 2) := by
  simpa using
    (realHilbertSumWeightedDiagonalLinearPMap_quadratic_lower_bound
      (G := G) w 0 hNonneg x)

end

end MathlibAnalytic
end MGAP4D