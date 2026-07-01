import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteResolventLagrange
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {ι E : Type*}
variable [DecidableEq ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The left distinguished-node Lagrange weight factors off the second node. -/
theorem finiteLagrangeWeight_insert_insert_left
    (parameter : ι → ℝ)
    (t : Finset ι)
    {a b : ι}
    (hab : a ≠ b)
    (ha : a ∉ t)
    (hb : b ∉ t) :
    finiteLagrangeWeight (insert a (insert b t)) parameter a =
      (parameter a - parameter b)⁻¹ *
        finiteLagrangeWeight (insert a t) parameter a := by
  simp [finiteLagrangeWeight, hab, hab.symm, ha, hb, Finset.prod_insert]

/-- The right distinguished-node Lagrange weight factors off the first node
with the sign dictated by reversing the node difference. -/
theorem finiteLagrangeWeight_insert_insert_right
    (parameter : ι → ℝ)
    (t : Finset ι)
    {a b : ι}
    (hab : a ≠ b)
    (ha : a ∉ t)
    (hb : b ∉ t) :
    finiteLagrangeWeight (insert a (insert b t)) parameter b =
      -(parameter a - parameter b)⁻¹ *
        finiteLagrangeWeight (insert b t) parameter b := by
  simp [finiteLagrangeWeight, hab, hab.symm, ha, hb, Finset.prod_insert]
  ring

/-- At every remaining node, the full Lagrange weight is the divided
difference of the two one-node-smaller weights. -/
theorem finiteLagrangeWeight_insert_insert_tail
    (parameter : ι → ℝ)
    (t : Finset ι)
    {a b x : ι}
    (hab : a ≠ b)
    (ha : a ∉ t)
    (hb : b ∉ t)
    (hx : x ∈ t)
    (hpa : parameter x ≠ parameter a)
    (hpb : parameter x ≠ parameter b)
    (habp : parameter a ≠ parameter b) :
    finiteLagrangeWeight (insert a (insert b t)) parameter x =
      (parameter a - parameter b)⁻¹ *
        (finiteLagrangeWeight (insert a t) parameter x -
          finiteLagrangeWeight (insert b t) parameter x) := by
  have hxa : x ≠ a := by
    intro h
    subst x
    exact ha hx
  have hxb : x ≠ b := by
    intro h
    subst x
    exact hb hx
  simp [finiteLagrangeWeight, hab, hab.symm, ha, hb, hx,
    hxa, hxa.symm, hxb, hxb.symm, Finset.prod_insert]
  field_simp [sub_ne_zero.mpr hpa, sub_ne_zero.mpr hpb,
    sub_ne_zero.mpr habp]
  <;> ring

/-- The closed finite Lagrange combination satisfies the same two-head
recursion as the finite resolvent divided difference. -/
theorem finiteLagrangeCombination_insert_insert_recursion
    (parameter : ι → ℝ)
    (A : ι → E →L[ℝ] E)
    (t : Finset ι)
    {a b : ι}
    (hab : a ≠ b)
    (ha : a ∉ t)
    (hb : b ∉ t)
    (hInjective :
      Set.InjOn parameter ((insert a (insert b t) : Finset ι) : Set ι)) :
    finiteLagrangeCombination (insert a (insert b t)) parameter A =
      (parameter a - parameter b)⁻¹ •
        (finiteLagrangeCombination (insert a t) parameter A -
          finiteLagrangeCombination (insert b t) parameter A) := by
  have habp : parameter a ≠ parameter b := by
    intro hp
    have := hInjective (by simp) (by simp) hp
    exact hab this
  have hTail :
      ∑ x ∈ t,
          finiteLagrangeWeight (insert a (insert b t)) parameter x • A x =
        (parameter a - parameter b)⁻¹ •
          ((∑ x ∈ t, finiteLagrangeWeight (insert a t) parameter x • A x) -
            ∑ x ∈ t, finiteLagrangeWeight (insert b t) parameter x • A x) := by
    calc
      ∑ x ∈ t,
          finiteLagrangeWeight (insert a (insert b t)) parameter x • A x =
        ∑ x ∈ t,
          ((parameter a - parameter b)⁻¹ *
            (finiteLagrangeWeight (insert a t) parameter x -
              finiteLagrangeWeight (insert b t) parameter x)) • A x := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxa : x ≠ a := by
              intro h
              subst x
              exact ha hx
            have hxb : x ≠ b := by
              intro h
              subst x
              exact hb hx
            have hpa : parameter x ≠ parameter a := by
              intro hp
              have hEq := hInjective (by simp [hx]) (by simp) hp
              exact hxa hEq
            have hpb : parameter x ≠ parameter b := by
              intro hp
              have hEq := hInjective (by simp [hx]) (by simp) hp
              exact hxb hEq
            rw [finiteLagrangeWeight_insert_insert_tail
              parameter t hab ha hb hx hpa hpb habp]
      _ = (parameter a - parameter b)⁻¹ •
          ((∑ x ∈ t, finiteLagrangeWeight (insert a t) parameter x • A x) -
            ∑ x ∈ t, finiteLagrangeWeight (insert b t) parameter x • A x) := by
        rw [smul_sub, Finset.smul_sum, Finset.smul_sum]
        apply congrArg₂ (· - ·)
        · apply Finset.sum_congr rfl
          intro x hx
          rw [smul_smul]
          rfl
        · apply Finset.sum_congr rfl
          intro x hx
          rw [smul_smul]
          rfl
  rw [finiteLagrangeCombination]
  rw [Finset.sum_insert (by simp [hab, hb]), Finset.sum_insert hb]
  rw [finiteLagrangeCombination, Finset.sum_insert ha]
  rw [finiteLagrangeCombination, Finset.sum_insert hb]
  rw [finiteLagrangeWeight_insert_insert_left parameter t hab ha hb]
  rw [finiteLagrangeWeight_insert_insert_right parameter t hab ha hb]
  rw [hTail]
  module

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
