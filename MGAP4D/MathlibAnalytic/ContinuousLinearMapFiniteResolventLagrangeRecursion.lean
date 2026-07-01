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
  have hEraseFull : (insert a (insert b t)).erase a = insert b t := by
    ext x
    simp [hab, ha]
  have hEraseSmall : (insert a t).erase a = t := by
    ext x
    simp [ha]
  unfold finiteLagrangeWeight
  rw [hEraseFull, hEraseSmall, Finset.prod_insert hb]
  simp only [mul_inv_rev₀]
  ring

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
  have hEraseFull : (insert a (insert b t)).erase b = insert a t := by
    ext x
    simp [hab, hb]
  have hEraseSmall : (insert b t).erase b = t := by
    ext x
    simp [hb]
  unfold finiteLagrangeWeight
  rw [hEraseFull, hEraseSmall, Finset.prod_insert ha]
  simp only [mul_inv_rev₀]
  rw [show parameter b - parameter a = -(parameter a - parameter b) by ring,
    inv_neg]
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
  have haErase : a ∉ t.erase x := by
    simp [ha]
  have hbErase : b ∉ t.erase x := by
    simp [hb]
  have haInsert : a ∉ insert b (t.erase x) := by
    simp [hab, haErase]
  have hEraseFull :
      (insert a (insert b t)).erase x =
        insert a (insert b (t.erase x)) := by
    ext y
    simp [hxa, hxb]
  have hEraseA : (insert a t).erase x = insert a (t.erase x) := by
    ext y
    simp [hxa]
  have hEraseB : (insert b t).erase x = insert b (t.erase x) := by
    ext y
    simp [hxb]
  unfold finiteLagrangeWeight
  rw [hEraseFull, hEraseA, hEraseB]
  rw [Finset.prod_insert haInsert, Finset.prod_insert hbErase,
    Finset.prod_insert haErase, Finset.prod_insert hbErase]
  simp only [mul_inv_rev₀]
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
    have hEq := hInjective (by simp) (by simp) hp
    exact hab hEq
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
      _ = ∑ x ∈ t,
          (parameter a - parameter b)⁻¹ •
            (finiteLagrangeWeight (insert a t) parameter x • A x -
              finiteLagrangeWeight (insert b t) parameter x • A x) := by
        apply Finset.sum_congr rfl
        intro x hx
        module
      _ = (parameter a - parameter b)⁻¹ •
          (∑ x ∈ t,
            (finiteLagrangeWeight (insert a t) parameter x • A x -
              finiteLagrangeWeight (insert b t) parameter x • A x)) := by
        rw [Finset.smul_sum]
      _ = (parameter a - parameter b)⁻¹ •
          ((∑ x ∈ t, finiteLagrangeWeight (insert a t) parameter x • A x) -
            ∑ x ∈ t, finiteLagrangeWeight (insert b t) parameter x • A x) := by
        rw [Finset.sum_sub_distrib]
  rw [finiteLagrangeCombination]
  rw [Finset.sum_insert (by simp [hab, ha]), Finset.sum_insert hb]
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
