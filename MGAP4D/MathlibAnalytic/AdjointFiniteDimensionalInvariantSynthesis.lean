import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

universe u v

variable {V : Type u} {W : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- Let `A : V → W` be a bounded operator and let `K ≤ V` be finite-dimensional.
If the normal operator `A† A` preserves `K` and `A` has trivial kernel on `K`,
then every vector of `K` lies in the exact range of the adjoint synthesis `A†`.

The proof uses Mathlib's exact identity
`ker (A† A) = ker A`.  Hence the restriction of `A† A` to `K` is injective;
finite-dimensionality turns that endomorphism into a surjection.  Solving the
restricted normal equation and applying `A` gives an explicit synthesis
preimage.

This is strictly weaker than requiring `A†` to be surjective on the whole
ambient Hilbert space and does not require the chosen vectors to be individual
eigenvectors of `A† A`. -/
theorem continuousLinearMap_adjoint_exists_preimage_of_finiteDimensional_invariant_submodule
    (A : V →L[ℝ] W) (K : Submodule ℝ V)
    [FiniteDimensional ℝ K]
    (hInvariant : ∀ x ∈ K, (A† ∘L A) x ∈ K)
    (hKernel : ∀ x ∈ K, A x = 0 → x = 0)
    {y : V} (hy : y ∈ K) :
    ∃ u : W, (A†) u = y := by
  let T : K →ₗ[ℝ] K :=
    (A† ∘L A).toLinearMap.restrict hInvariant
  have hTInjective : Function.Injective T := by
    intro x z hxz
    have hval := congrArg Subtype.val hxz
    change (A† ∘L A) (x : V) = (A† ∘L A) (z : V) at hval
    have hnormalZero : (A† ∘L A) ((x : V) - (z : V)) = 0 := by
      rw [map_sub, hval, sub_self]
    have hker : ((x : V) - (z : V)) ∈ (A† ∘L A).ker := by
      change (A† ∘L A) ((x : V) - (z : V)) = 0
      exact hnormalZero
    rw [A.ker_adjoint_comp_self] at hker
    have hAZero : A ((x : V) - (z : V)) = 0 := by
      change A ((x : V) - (z : V)) = 0 at hker
      exact hker
    have hzero : (x : V) - (z : V) = 0 :=
      hKernel ((x : V) - (z : V)) (K.sub_mem x.property z.property) hAZero
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  have hTSurjective : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := T) rfl).mp hTInjective
  rcases hTSurjective ⟨y, hy⟩ with ⟨v, hv⟩
  refine ⟨A (v : V), ?_⟩
  have hv' := congrArg Subtype.val hv
  change (A† ∘L A) (v : V) = y at hv'
  simpa using hv'

/-- Equivalent range formulation of the finite-dimensional invariant-sector
synthesis theorem. -/
theorem finiteDimensional_invariant_submodule_le_adjoint_range
    (A : V →L[ℝ] W) (K : Submodule ℝ V)
    [FiniteDimensional ℝ K]
    (hInvariant : ∀ x ∈ K, (A† ∘L A) x ∈ K)
    (hKernel : ∀ x ∈ K, A x = 0 → x = 0) :
    K ≤ (A†).range := by
  intro y hy
  rcases
      continuousLinearMap_adjoint_exists_preimage_of_finiteDimensional_invariant_submodule
        A K hInvariant hKernel hy with ⟨u, hu⟩
  exact ⟨u, hu⟩

end

end MathlibAnalytic
end MGAP4D
