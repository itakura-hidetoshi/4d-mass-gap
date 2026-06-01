import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearMap
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinition

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Graph carrier of the dense-domain bundled linear map, expressed back as a set
of ambient Hilbert-pairs. -/
def concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier :
    Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier) :=
  {p | ∃ x : concreteL2R2DenseDiagonalDomainCarrier,
    p.1 = concreteL2R2DenseDiagonalDomainCarrierVal x ∧
    p.2 = concreteL2R2DenseDiagonalDomainLinearMap x}

/-- Every point of the dense-domain bundled linear-map graph satisfies the
existing completed diagonal graph-carrier relation. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_completed_graph_carrier :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ⊆
      concreteL2R2CompletedDiagonalGraphCarrier := by
  intro p hp
  rcases hp with ⟨x, hp1, hp2⟩
  intro n
  rw [hp2, hp1]
  simpa [concreteL2R2WeightedCoordinate] using
    concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord x n

/-- A dense-domain input paired with its bundled linear-map value belongs to the
existing completed diagonal graph carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_pair_mem_completed_graph_carrier
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalGraphCarrier := by
  apply concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_completed_graph_carrier
  exact ⟨x, rfl, rfl⟩

/-- Every dense-domain input lies in the graph-defined completed diagonal
operator's domain carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_carrier_mem_completed_operator_domain
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    concreteL2R2DenseDiagonalDomainCarrierVal x ∈
      concreteL2R2CompletedDiagonalOperatorDomainCarrier := by
  refine ⟨concreteL2R2DenseDiagonalDomainLinearMap x, ?_⟩
  exact concrete_l2_r2_dense_diagonal_domain_linear_map_pair_mem_completed_graph_carrier x

/-- Dense-domain linear-map graph agreement surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearMapGraphAgreementSurface where
  linearMapReady : concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapSurfaceReady
  linearMapGraphCarrier : Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
  graphSubsetCompletedCarrier :
    linearMapGraphCarrier ⊆ concreteL2R2CompletedDiagonalGraphCarrier
  pairMemCompletedCarrier :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      (concreteL2R2DenseDiagonalDomainCarrierVal x,
        concreteL2R2DenseDiagonalDomainLinearMap x) ∈
          concreteL2R2CompletedDiagonalGraphCarrier
  domainProjection :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      concreteL2R2DenseDiagonalDomainCarrierVal x ∈
        concreteL2R2CompletedDiagonalOperatorDomainCarrier
  boundaryNotReverseGraphCarrierEquality : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain linear-map graph agreement surface. -/
def concreteL2R2DenseDiagonalDomainLinearMapGraphAgreementSurface :
    ConcreteL2R2DenseDiagonalDomainLinearMapGraphAgreementSurface :=
  { linearMapReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_surface_ready
    linearMapGraphCarrier := concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier
    graphSubsetCompletedCarrier :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_completed_graph_carrier
    pairMemCompletedCarrier :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_pair_mem_completed_graph_carrier
    domainProjection :=
      concrete_l2_r2_dense_diagonal_domain_carrier_mem_completed_operator_domain
    boundaryNotReverseGraphCarrierEquality := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the dense-domain linear-map graph agreement surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapSurfaceReady ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ⊆
    concreteL2R2CompletedDiagonalGraphCarrier ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalGraphCarrier) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    concreteL2R2DenseDiagonalDomainCarrierVal x ∈
      concreteL2R2CompletedDiagonalOperatorDomainCarrier) ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphAgreementSurface.boundaryNotReverseGraphCarrierEquality ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphAgreementSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphAgreementSurface.boundaryNotSelfAdjointness

/-- The dense-domain linear-map graph agreement surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_agreement_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_completed_graph_carrier,
    concrete_l2_r2_dense_diagonal_domain_linear_map_pair_mem_completed_graph_carrier,
    concrete_l2_r2_dense_diagonal_domain_carrier_mem_completed_operator_domain,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the bundled dense-domain linear-map graph is now certified
inside the existing completed graph carrier, but the reverse equality and closed
operator theorem remain future work. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementSurfaceReady

/-- Boundary theorem for dense-domain linear-map graph agreement. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_agreement_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphAgreementBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_agreement_surface_ready

end

end MathlibAnalytic
end MGAP4D
