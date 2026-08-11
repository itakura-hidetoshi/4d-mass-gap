import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Submodule
open scoped InnerProduct InnerProductSpace

noncomputable section

universe u v w

variable {V : Type u} {W : Type v} {ι : Type w}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- If `v` is linearly independent and its actual analysis images `A (v i)`
are still linearly independent, then the normal outputs `A† A (v i)` are
linearly independent as well.

The key Mathlib identity is `ker (A† A) = ker A`.  Linear independence of the
analysis images makes `A` injective on `span(range v)`, hence the same is true
of `A† A`; `LinearIndependent.map_injOn` then transports independence through
the normal operator.

This theorem requires no invariant-subspace or surjectivity assumption. -/
theorem continuousLinearMap_adjoint_comp_self_linearIndependent_of_map_linearIndependent
    (A : V →L[ℝ] W) (v : ι → V)
    (hv : LinearIndependent ℝ v)
    (hAv : LinearIndependent ℝ (fun i => A (v i))) :
    LinearIndependent ℝ (fun i => (A† ∘L A) (v i)) := by
  have hdisjA :
      Disjoint (Submodule.span ℝ (Set.range v)) (LinearMap.ker A.toLinearMap) := by
    apply Submodule.range_ker_disjoint (v := v) (f := A.toLinearMap)
    simpa [Function.comp_def] using hAv
  have hnormalInj :
      Set.InjOn (A† ∘L A).toLinearMap (Submodule.span ℝ (Set.range v)) := by
    intro x hx y hy hxy
    have hsubSpan : x - y ∈ Submodule.span ℝ (Set.range v) :=
      Submodule.sub_mem _ hx hy
    have hsubKerNormal : x - y ∈ (A† ∘L A).ker := by
      change (A† ∘L A) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hsubKerA : x - y ∈ A.ker := by
      rw [A.ker_adjoint_comp_self] at hsubKerNormal
      exact hsubKerNormal
    have hzero : x - y = 0 :=
      Submodule.disjoint_def.mp hdisjA (x - y) hsubSpan hsubKerA
    exact sub_eq_zero.mp hzero
  have hmapped := hv.map_injOn (A† ∘L A).toLinearMap hnormalInj
  simpa [Function.comp_def] using hmapped

end

end MathlibAnalytic
end MGAP4D
