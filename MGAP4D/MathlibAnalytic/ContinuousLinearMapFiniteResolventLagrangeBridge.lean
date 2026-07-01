import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteResolventLagrangeRecursion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α E : Type*}
variable [DecidableEq α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pairwise distinct parameter values on a list make the parameter map
injective on the finite set underlying that list. -/
theorem injOn_toFinset_of_pairwise_parameter_ne
    (parameter : α → ℝ)
    (s : List α)
    (hPairwise : s.Pairwise fun a b => parameter a ≠ parameter b) :
    Set.InjOn parameter ((s.toFinset : Finset α) : Set α) := by
  induction s with
  | nil =>
      simp
  | cons a s ih =>
      rcases List.pairwise_cons.mp hPairwise with ⟨ha, hs⟩
      have ihs := ih hs
      intro x hx y hy hxy
      change x ∈ (a :: s).toFinset at hx
      change y ∈ (a :: s).toFinset at hy
      simp only [List.toFinset_cons, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · exfalso
          exact (ha y (by simpa using hy)) hxy
      · rcases hy with rfl | hy
        · exfalso
          exact (ha x (by simpa using hx)) hxy.symm
        · exact ihs (by simpa using hx) (by simpa using hy) hxy

/-- Closed Lagrange normal form of a finite operator-value list.  The empty
list is normalized to the identity operator, matching the empty ordered
product and the recursive divided-difference convention. -/
def finiteResolventLagrangeNormalForm
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E) :
    List α → E →L[ℝ] E
  | [] => 1
  | a :: s => finiteLagrangeCombination (a :: s).toFinset parameter A

@[simp] theorem finiteResolventLagrangeNormalForm_nil
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E) :
    finiteResolventLagrangeNormalForm parameter A [] = 1 := rfl

@[simp] theorem finiteResolventLagrangeNormalForm_cons
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E)
    (a : α)
    (s : List α) :
    finiteResolventLagrangeNormalForm parameter A (a :: s) =
      finiteLagrangeCombination (a :: s).toFinset parameter A := rfl

/-- On every finite list with pairwise distinct parameter values, the recursive
resolvent divided difference is exactly the closed barycentric Lagrange normal
form. -/
theorem finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E)
    (s : List α)
    (hPairwise : s.Pairwise fun a b => parameter a ≠ parameter b) :
    finiteResolventDividedDifference parameter A s =
      finiteResolventLagrangeNormalForm parameter A s := by
  cases s with
  | nil =>
      simp [finiteResolventDividedDifference]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [finiteResolventDividedDifference,
            finiteResolventLagrangeNormalForm]
      | cons b tail =>
          rw [finiteResolventDividedDifference_cons_cons]
          rcases List.pairwise_cons.mp hPairwise with ⟨haRel, hBTail⟩
          rcases List.pairwise_cons.mp hBTail with ⟨hbRel, hTail⟩
          have habParameter : parameter a ≠ parameter b :=
            haRel b (by simp)
          have hab : a ≠ b := by
            intro h
            subst b
            exact habParameter rfl
          have ha : a ∉ tail.toFinset := by
            intro h
            have hmem : a ∈ tail := by simpa using h
            exact (haRel a (by simp [hmem])) rfl
          have hb : b ∉ tail.toFinset := by
            intro h
            have hmem : b ∈ tail := by simpa using h
            exact (hbRel b hmem) rfl
          have hATail :
              (a :: tail).Pairwise fun x y => parameter x ≠ parameter y := by
            apply List.pairwise_cons.mpr
            constructor
            · intro x hx
              exact haRel x (by simp [hx])
            · exact hTail
          have ihA :=
            finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
              parameter A (a :: tail) hATail
          have ihB :=
            finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
              parameter A (b :: tail) hBTail
          rw [ihA, ihB]
          have hInjectiveFull :
              Set.InjOn parameter
                (((a :: b :: tail).toFinset : Finset α) : Set α) :=
            injOn_toFinset_of_pairwise_parameter_ne
              parameter (a :: b :: tail) hPairwise
          have hInjective :
              Set.InjOn parameter
                ((insert a (insert b tail.toFinset) : Finset α) : Set α) := by
            simpa using hInjectiveFull
          have hRec :=
            finiteLagrangeCombination_insert_insert_recursion
              parameter A tail.toFinset hab ha hb hInjective
          simpa [finiteResolventLagrangeNormalForm] using hRec.symm
termination_by s.length

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
