import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace MGAP4D
namespace MathlibAnalytic

open ContinuousLinearMap InnerProductSpace

noncomputable section

/-- A coercive Lax--Milgram operator that factors through `S` forces `S` to be
surjective.

This is the generic Hilbert-space mechanism needed by the finite Wilson
boundary-synthesis route.  If a bounded bilinear form `B` on the target Hilbert
space is coercive and its Riesz operator factors as

`B♯ = S ∘ A`,

then Lax--Milgram makes `B♯` onto.  Every target vector therefore has the form
`S (A x)`, so `S` itself is onto.

No adjoint hypothesis is needed at this generic layer.  In the Wilson
specialization one may take `A = S†`, so a coercive lower bound for `S S†`
produces surjectivity of the actual boundary synthesis operator. -/
theorem continuousLinearMap_surjective_of_laxMilgram_factorization
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : W →L[ℝ] V)
    (A : V →L[ℝ] W)
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hfactor : ∀ v,
      InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B v = S (A v))
    (hcoercive : IsCoercive B) :
    Function.Surjective S := by
  intro y
  have hy :
      y ∈ (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B).range := by
    rw [hcoercive.range_eq_top]
    exact Submodule.mem_top
  rcases hy with ⟨x, hx⟩
  refine ⟨A x, ?_⟩
  rw [← hfactor x]
  exact hx

/-- Pointwise witness form of the factorized Lax--Milgram surjectivity theorem. -/
theorem exists_preimage_of_laxMilgram_factorization
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : W →L[ℝ] V)
    (A : V →L[ℝ] W)
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hfactor : ∀ v,
      InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B v = S (A v))
    (hcoercive : IsCoercive B)
    (y : V) :
    ∃ x : W, S x = y :=
  continuousLinearMap_surjective_of_laxMilgram_factorization
    S A B hfactor hcoercive y

end

end MathlibAnalytic
end MGAP4D
