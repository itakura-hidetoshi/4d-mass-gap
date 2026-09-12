import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped LinearPMap

/-- A sequential graph-approximation criterion for Mathlib `LinearPMap.HasCore`.

If `C` is contained in the domain of a closed partially-defined operator `A`,
and every graph point `(x, A x)` is the limit of graph points whose first
coordinates lie in `C`, then restricting `A` to `C` and closing recovers `A`.
This is the standard graph-core criterion, phrased directly in the Mathlib API. -/
theorem realLinearPMap_hasCore_of_seq_graph_approximation
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →ₗ.[ℝ] F)
    (C : Submodule ℝ E)
    (hC : C ≤ A.domain)
    (hAClosed : A.IsClosed)
    (hApprox : ∀ x : A.domain,
      ∃ u : ℕ → C,
        Tendsto (fun n => (u n : E)) atTop (𝓝 (x : E)) ∧
        Tendsto
          (fun n => A ⟨(u n : E), hC (u n).property⟩)
          atTop
          (𝓝 (A x))) :
    A.HasCore C := by
  let R : E →ₗ.[ℝ] F := A.domRestrict C
  have hRleA : R ≤ A := by
    change A.domRestrict C ≤ A
    exact LinearPMap.domRestrict_le
  have hRClosable : R.IsClosable :=
    hAClosed.isClosable.leIsClosable hRleA
  have hGraphClosure : R.graph.topologicalClosure = A.graph := by
    apply le_antisymm
    · rw [← hAClosed.submodule_topologicalClosure_eq]
      exact Submodule.topologicalClosure_mono
        (LinearPMap.le_graph_of_le hRleA)
    · intro p hp
      rw [LinearPMap.mem_graph_iff] at hp
      rcases hp with ⟨x, hxBase, hxValue⟩
      have hpEq : ((x : E), A x) = p := by
        exact Prod.ext hxBase hxValue
      rw [← hpEq]
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
        mem_closure_iff_seq_limit]
      rcases hApprox x with ⟨u, huBase, huValue⟩
      let v : ℕ → E × F := fun n =>
        ((u n : E), A ⟨(u n : E), hC (u n).property⟩)
      refine ⟨v, ?_, ?_⟩
      · intro n
        change v n ∈ R.graph
        apply (LinearPMap.mem_graph_iff' R).2
        let y : R.domain :=
          ⟨(u n : E), by
            change (u n : E) ∈ C ⊓ A.domain
            exact ⟨(u n).property, hC (u n).property⟩⟩
        refine ⟨y, ?_⟩
        apply Prod.ext
        · rfl
        · change R y = A ⟨(u n : E), hC (u n).property⟩
          simpa only [R] using
            (LinearPMap.domRestrict_apply
              (x := y)
              (y := ⟨(u n : E), hC (u n).property⟩) rfl)
      · change Tendsto
          (fun n => ((u n : E), A ⟨(u n : E), hC (u n).property⟩))
          atTop
          (𝓝 ((x : E), A x))
        rw [nhds_prod_eq]
        exact huBase.prodMk huValue
  refine ⟨hC, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hRClosable.graph_closure_eq_closure_graph]
  exact hGraphClosure

end

end MathlibAnalytic
end MGAP4D
