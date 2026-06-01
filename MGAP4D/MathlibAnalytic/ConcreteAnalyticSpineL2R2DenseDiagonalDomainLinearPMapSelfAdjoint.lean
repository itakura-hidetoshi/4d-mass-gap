import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequences

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- A point of the Mathlib graph-adjoint submodule satisfies the existing
carrier-level formal-adjoint graph candidate predicate. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_subset_formal_adjoint_candidate :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint :
        Submodule ℝ (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) :
          Set ConcreteL2R2PairSpace) ⊆
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  intro p hp
  rcases p with ⟨y, w⟩
  intro z Tz hzgraph
  have hzcompleted :
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphCarrier := by
    rw [← concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq]
    exact hzgraph
  have hzTgraph :
      (z, Tz) ∈ concreteL2R2DenseDiagonalDomainLinearPMap.graph := by
    show (z, Tz) ∈
      ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
        Set ConcreteL2R2PairSpace))
    rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier]
    exact hzcompleted
  have hadj :=
    (Submodule.mem_adjoint_iff concreteL2R2DenseDiagonalDomainLinearPMap.graph (y, w)).1
      hp z Tz hzTgraph
  have hpair : inner ℝ Tz y = inner ℝ z w := by
    exact sub_eq_zero.mp hadj
  calc
    inner ℝ w z = inner ℝ z w := concrete_l2_r2_inner_product_comm w z
    _ = inner ℝ Tz y := hpair.symm
    _ = inner ℝ y Tz := concrete_l2_r2_inner_product_comm Tz y

/-- The Mathlib graph-adjoint submodule is contained in the original dense-domain
`LinearPMap` graph. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_le_graph :
    concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint ≤
      concreteL2R2DenseDiagonalDomainLinearPMap.graph := by
  intro p hp
  have hcandidate :
      (p : ConcreteL2R2PairSpace) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate :=
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_subset_formal_adjoint_candidate hp
  have hcarrier :
      (p : ConcreteL2R2PairSpace) ∈
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier :=
    (concrete_l2_r2_formal_adjoint_candidate_mem_iff_completed_diagonal_graph p).1 hcandidate
  have hcompleted :
      (p : ConcreteL2R2PairSpace) ∈ concreteL2R2CompletedDiagonalGraphCarrier := by
    rw [← concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq]
    exact hcarrier
  show p ∈
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
      Set ConcreteL2R2PairSpace))
  rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier]
  exact hcompleted

/-- The dense-domain diagonal `LinearPMap` graph is fixed by Mathlib graph-adjoint. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph :
    concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint =
      concreteL2R2DenseDiagonalDomainLinearPMap.graph := by
  exact le_antisymm
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_le_graph
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_le_graph_adjoint

/-- The actual Mathlib adjoint of the dense-domain diagonal `LinearPMap` is the
operator itself. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self_of_graph_adjoint_fixed_point
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph

/-- The dense-domain diagonal `LinearPMap` is self-adjoint in Mathlib's actual
`IsSelfAdjoint` sense. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact LinearPMap.isSelfAdjoint_def.mpr
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self

/-- Self-adjointness surface for the dense-domain diagonal `LinearPMap`. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurface where
  adjointInclusionConsequencesReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurfaceReady
  graphAdjointSubsetFormalAdjointCandidate :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint :
        Submodule ℝ (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) :
          Set ConcreteL2R2PairSpace) ⊆
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate
  graphAdjointLeGraph :
    concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint ≤
      concreteL2R2DenseDiagonalDomainLinearPMap.graph
  graphAdjointEqGraph :
    concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint =
      concreteL2R2DenseDiagonalDomainLinearPMap.graph
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  isSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap

/-- Concrete self-adjointness surface for the dense-domain diagonal `LinearPMap`. -/
def concreteL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurface :=
  { adjointInclusionConsequencesReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_consequences_surface_ready
    graphAdjointSubsetFormalAdjointCandidate :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_subset_formal_adjoint_candidate
    graphAdjointLeGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_le_graph
    graphAdjointEqGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    isSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint }

/-- Readiness predicate for the dense-domain diagonal `LinearPMap` self-adjointness
surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurfaceReady ∧
  concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint ≤
    concreteL2R2DenseDiagonalDomainLinearPMap.graph ∧
  concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint =
    concreteL2R2DenseDiagonalDomainLinearPMap.graph ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap

/-- The dense-domain diagonal `LinearPMap` self-adjointness surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_consequences_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_le_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint⟩

end

end MathlibAnalytic
end MGAP4D