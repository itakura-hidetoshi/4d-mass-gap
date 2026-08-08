import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementKernelCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Four-point mixed cross difference of a finite real kernel. -/
def finiteKernelMixedCrossDifference
    {α : Type}
    (K : α → α → ℝ)
    (x x' y y' : α) : ℝ :=
  (K x y - K x y') - (K x' y - K x' y')

/-- A nonzero four-point mixed cross difference is an explicit certificate that
the uniform-average complement-to-complement kernel block is nonzero.

This is the converse witness direction needed after Package W: no explicit
centering of the whole finite kernel is required.  The proof tests the operator
on the zero-mass source vector `δ_x - δ_x'` and then compares the two output
coordinates `y,y'`. -/
theorem finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_ne_zero_of_mixedCrossDifference_ne_zero
    {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    (K : α → α → ℝ)
    (x x' y y' : α)
    (hMixed : finiteKernelMixedCrossDifference K x x' y y' ≠ 0) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator K).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) ≠ 0 := by
  have hxx' : x ≠ x' := by
    intro h
    subst x'
    simp [finiteKernelMixedCrossDifference] at hMixed
  have hx'x : x' ≠ x := Ne.symm hxx'
  let f : FiniteBoundaryHilbert α :=
    WithLp.toLp 2 (fun z : α => if z = x then (1 : ℝ)
      else if z = x' then (-1 : ℝ) else 0)
  have hsum : (∑ z : α, f z) = 0 := by
    dsimp [f]
    simp [hxx']
  have hQf : finiteUniformAverageComplementLinearMap f = f := by
    ext z
    rw [finiteUniformAverageComplementLinearMap_apply, hsum]
    ring
  have hKfy : finiteKernelOperator K f y = K x y - K x' y := by
    rw [finiteKernelOperator_apply]
    dsimp [f]
    calc
      (∑ z : α,
          if z = x then K z y
          else if z = x' then -K z y else 0) =
        (∑ z : α, if z = x then K x y else 0) +
          (∑ z : α, if z = x' then -K x' y else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hz : z = x
        · subst z
          simp [hxx']
        · by_cases hz' : z = x'
          · subst z
            simp [hxx', hx'x]
          · simp [hz, hz']
      _ = K x y + (-K x' y) := by simp
      _ = K x y - K x' y := by ring
  have hKfy' : finiteKernelOperator K f y' = K x y' - K x' y' := by
    rw [finiteKernelOperator_apply]
    dsimp [f]
    calc
      (∑ z : α,
          if z = x then K z y'
          else if z = x' then -K z y' else 0) =
        (∑ z : α, if z = x then K x y' else 0) +
          (∑ z : α, if z = x' then -K x' y' else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hz : z = x
        · subst z
          simp [hxx']
        · by_cases hz' : z = x'
          · subst z
            simp [hxx', hx'x]
          · simp [hz, hz']
      _ = K x y' + (-K x' y') := by simp
      _ = K x y' - K x' y' := by ring
  intro hzero
  have hz := LinearMap.congr_fun hzero f
  change
    finiteUniformAverageComplementLinearMap
      (finiteKernelOperator K (finiteUniformAverageComplementLinearMap f)) = 0 at hz
  rw [hQf] at hz
  have hy :
      finiteUniformAverageComplementLinearMap (finiteKernelOperator K f) y = 0 := by
    simpa using congrArg (fun g : FiniteBoundaryHilbert α => g y) hz
  have hy' :
      finiteUniformAverageComplementLinearMap (finiteKernelOperator K f) y' = 0 := by
    simpa using congrArg (fun g : FiniteBoundaryHilbert α => g y') hz
  rw [finiteUniformAverageComplementLinearMap_apply] at hy hy'
  have hout : finiteKernelOperator K f y - finiteKernelOperator K f y' = 0 := by
    linear_combination hy - hy'
  rw [hKfy, hKfy'] at hout
  apply hMixed
  unfold finiteKernelMixedCrossDifference
  linear_combination hout

end

end MathlibAnalytic
end MGAP4D
