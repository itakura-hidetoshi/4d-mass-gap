import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelPerronOrder
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Once a strictly-positive fixed vector exists for a positivity-improving
normalized finite kernel, every other fixed vector lies on the same real
line. -/
theorem finiteKernelNormalizedOperator_fixed_eq_smul_of_pointwisePositive_fixed
    {α : Type} [Fintype α] [Nonempty α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (p g : FiniteBoundaryHilbert α)
    (hp : FiniteBoundaryPointwisePositive p)
    (hpfix : finiteKernelNormalizedOperator kernel p = p)
    (hgfix : finiteKernelNormalizedOperator kernel g = g) :
    ∃ c : ℝ, g = c • p := by
  classical
  obtain ⟨x₀, hx₀⟩ :=
    Finite.exists_max (fun x : α => g x / p x)
  let c : ℝ := g x₀ / p x₀
  let h : FiniteBoundaryHilbert α := c • p - g
  have hh_nonneg : FiniteBoundaryPointwiseNonnegative h := by
    intro x
    have hpx : 0 < p x := hp x
    have hratio : g x / p x ≤ c := by
      simpa [c] using hx₀ x
    have hmul : g x ≤ c * p x :=
      (div_le_iff₀ hpx).mp hratio
    change 0 ≤ c * p x - g x
    exact sub_nonneg.mpr hmul
  have hhfix : finiteKernelNormalizedOperator kernel h = h := by
    calc
      finiteKernelNormalizedOperator kernel h =
          c • finiteKernelNormalizedOperator kernel p -
            finiteKernelNormalizedOperator kernel g := by
        simp [h]
      _ = c • p - g := by rw [hpfix, hgfix]
      _ = h := rfl
  have hhx₀ : h x₀ = 0 := by
    change c * p x₀ - g x₀ = 0
    rw [sub_eq_zero]
    exact div_mul_cancel₀ (g x₀) (ne_of_gt (hp x₀))
  have hhzero : h = 0 := by
    by_contra hhne
    have hpos :=
      finiteKernelNormalizedOperator_pointwisePositive
        kernel hkernel h hh_nonneg hhne x₀
    rw [hhfix] at hpos
    rw [hhx₀] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨c, ?_⟩
  exact (sub_eq_zero.mp hhzero).symm

/-- The fixed-point space of a normalized strictly-positive finite kernel is
subsingleton modulo scalar multiplication by any chosen strictly-positive
fixed vector. -/
theorem finiteKernelNormalizedOperator_fixed_pair_linearlyDependent
    {α : Type} [Fintype α] [Nonempty α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (p : FiniteBoundaryHilbert α)
    (hp : FiniteBoundaryPointwisePositive p)
    (hpfix : finiteKernelNormalizedOperator kernel p = p)
    (f g : FiniteBoundaryHilbert α)
    (hffix : finiteKernelNormalizedOperator kernel f = f)
    (hgfix : finiteKernelNormalizedOperator kernel g = g) :
    ∃ a b : ℝ, f = a • p ∧ g = b • p := by
  obtain ⟨a, ha⟩ :=
    finiteKernelNormalizedOperator_fixed_eq_smul_of_pointwisePositive_fixed
      kernel hkernel p f hp hpfix hffix
  obtain ⟨b, hb⟩ :=
    finiteKernelNormalizedOperator_fixed_eq_smul_of_pointwisePositive_fixed
      kernel hkernel p g hp hpfix hgfix
  exact ⟨a, b, ha, hb⟩

end

end MathlibAnalytic
end MGAP4D
