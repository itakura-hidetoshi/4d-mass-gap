import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreement

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The completed graph carrier restricted to inputs that already lie in the
promoted dense diagonal-domain submodule. -/
def concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain :
    Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier) :=
  {p | p ∈ concreteL2R2CompletedDiagonalGraphCarrier ∧
    p.1 ∈ (concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier)}

/-- A point of the restricted completed graph carrier gives a dense-domain
carrier witness for its input. -/
def concreteL2R2DenseDomainCarrierOfRestrictedGraphPoint
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
    (hp : p ∈ concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain) :
    concreteL2R2DenseDiagonalDomainCarrier :=
  ⟨p.1, hp.2⟩

/-- The dense-domain carrier extracted from a restricted graph point has exactly
that graph point's input as its ambient value. -/
theorem concrete_l2_r2_dense_domain_carrier_of_restricted_graph_point_val
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
    (hp : p ∈ concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain) :
    concreteL2R2DenseDiagonalDomainCarrierVal
      (concreteL2R2DenseDomainCarrierOfRestrictedGraphPoint p hp) = p.1 := by
  rfl

/-- On a restricted completed graph point, the existing completed graph output is
exactly the dense-domain bundled linear-map output. -/
theorem concrete_l2_r2_restricted_completed_graph_output_eq_dense_linear_map
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
    (hp : p ∈ concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain) :
    p.2 =
      concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDomainCarrierOfRestrictedGraphPoint p hp) := by
  ext n
  have hgraph : p ∈ concreteL2R2CompletedDiagonalGraphCarrier := hp.1
  have hcoord := hgraph n
  have hlin :=
    concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord
      (concreteL2R2DenseDomainCarrierOfRestrictedGraphPoint p hp) n
  rw [hcoord]
  rw [hlin]
  rfl

/-- The restricted completed graph carrier is contained in the dense-domain
bundled linear-map graph carrier. -/
theorem concrete_l2_r2_restricted_completed_graph_subset_dense_diagonal_domain_linear_map_graph :
    concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain ⊆
      concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier := by
  intro p hp
  refine ⟨concreteL2R2DenseDomainCarrierOfRestrictedGraphPoint p hp, ?_, ?_⟩
  · exact (concrete_l2_r2_dense_domain_carrier_of_restricted_graph_point_val p hp).symm
  · exact concrete_l2_r2_restricted_completed_graph_output_eq_dense_linear_map p hp

/-- The dense-domain bundled linear-map graph carrier is exactly the completed
diagonal graph carrier restricted to dense-domain inputs. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_restricted_completed_graph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
      concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain := by
  apply Set.Subset.antisymm
  · intro p hp
    exact ⟨
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_completed_graph_carrier hp,
      by
        rcases hp with ⟨x, hp1, _⟩
        rw [hp1]
        exact x.2⟩
  · exact concrete_l2_r2_restricted_completed_graph_subset_dense_diagonal_domain_linear_map_graph

/-- Restricted reverse graph agreement surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearMapGraphReverseSurface where
  graphAgreementReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementSurfaceReady
  restrictedCompletedGraphCarrier :
    Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
  restrictedSubsetLinearMapGraph :
    restrictedCompletedGraphCarrier ⊆ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier
  graphEqRestrictedCompletedGraph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier = restrictedCompletedGraphCarrier
  boundaryNotUnrestrictedGraphCarrierEquality : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete restricted reverse graph agreement surface. -/
def concreteL2R2DenseDiagonalDomainLinearMapGraphReverseSurface :
    ConcreteL2R2DenseDiagonalDomainLinearMapGraphReverseSurface :=
  { graphAgreementReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_agreement_surface_ready
    restrictedCompletedGraphCarrier :=
      concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain
    restrictedSubsetLinearMapGraph :=
      concrete_l2_r2_restricted_completed_graph_subset_dense_diagonal_domain_linear_map_graph
    graphEqRestrictedCompletedGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_restricted_completed_graph
    boundaryNotUnrestrictedGraphCarrierEquality := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for restricted reverse graph agreement. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementSurfaceReady ∧
  concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain ⊆
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphReverseSurface.boundaryNotUnrestrictedGraphCarrierEquality ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphReverseSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphReverseSurface.boundaryNotSelfAdjointness

/-- The restricted reverse graph agreement surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_reverse_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_agreement_surface_ready,
    concrete_l2_r2_restricted_completed_graph_subset_dense_diagonal_domain_linear_map_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_restricted_completed_graph,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: graph equality is now proved on the promoted dense-domain
restriction.  The unrestricted graph-carrier equality remains a separate maximal
domain/closure problem. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseSurfaceReady

/-- Boundary theorem for restricted reverse graph agreement. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_reverse_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_reverse_surface_ready

end

end MathlibAnalytic
end MGAP4D
