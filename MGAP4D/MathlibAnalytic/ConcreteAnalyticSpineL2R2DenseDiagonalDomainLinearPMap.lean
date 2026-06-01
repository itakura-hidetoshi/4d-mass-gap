import Mathlib.Analysis.InnerProductSpace.LinearPMap
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainActualAdjointPromotionObligation

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- The dense-domain diagonal action bundled as Mathlib's actual partially-defined
linear operator (`LinearPMap`). -/
def concreteL2R2DenseDiagonalDomainLinearPMap :
    ConcreteL2R1HilbertCarrier →ₗ.[ℝ] ConcreteL2R1HilbertCarrier :=
  { domain := concreteL2R2DiagonalDomainCandidateSubmodule
    toFun := concreteL2R2DenseDiagonalDomainLinearMap }

/-- The domain of the dense-domain `LinearPMap` is the promoted diagonal-domain
candidate submodule. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain :
    concreteL2R2DenseDiagonalDomainLinearPMap.domain =
      concreteL2R2DiagonalDomainCandidateSubmodule := by
  rfl

/-- Application of the dense-domain `LinearPMap` is the bundled dense-domain
linear map. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_apply
    (x : concreteL2R2DenseDiagonalDomainLinearPMap.domain) :
    concreteL2R2DenseDiagonalDomainLinearPMap x =
      concreteL2R2DenseDiagonalDomainLinearMap
        (x : concreteL2R2DenseDiagonalDomainCarrier) := by
  rfl

/-- The graph of the dense-domain `LinearPMap`, viewed as a set of ambient Hilbert
pairs, is exactly the previously constructed dense-domain graph carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_dense_graph_carrier :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
        Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier) := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hx1, hx2⟩
    refine ⟨(x : concreteL2R2DenseDiagonalDomainCarrier), ?_, ?_⟩
    · exact hx1.symm
    · simpa [concreteL2R2DenseDiagonalDomainLinearPMap] using hx2.symm
  · intro hp
    rcases hp with ⟨x, hp1, hp2⟩
    rw [LinearPMap.mem_graph_iff]
    refine ⟨x, ?_, ?_⟩
    · exact hp1.symm
    · simpa [concreteL2R2DenseDiagonalDomainLinearPMap] using hp2.symm

/-- The graph of the dense-domain `LinearPMap` is exactly the completed diagonal
graph carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
        Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2CompletedDiagonalGraphCarrier) := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_dense_graph_carrier]
  exact concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier

/-- The graph of the dense-domain `LinearPMap` is exactly the existing formal
adjoint linear-map graph. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_formal_adjoint_linear_map_graph :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
        Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_dense_graph_carrier]
  exact concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph

/-- The dense-domain `LinearPMap` is closed in Mathlib's `LinearPMap.IsClosed`
sense. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap := by
  rw [LinearPMap.IsClosed]
  rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_dense_graph_carrier]
  exact concrete_l2_r2_dense_diagonal_domain_linear_map_graph_isClosed

/-- The dense-domain `LinearPMap` has dense domain. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain :
    Dense ((concreteL2R2DenseDiagonalDomainLinearPMap.domain :
      Set ConcreteL2R1HilbertCarrier)) := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain]
  exact concrete_l2_r2_diagonal_domain_candidate_submodule_dense

/-- LinearPMap promotion surface for the dense-domain diagonal operator. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapSurface where
  actualAdjointPromotionObligationReady :
    concreteL2R2DenseDiagonalDomainActualAdjointPromotionObligation
  pmap : ConcreteL2R1HilbertCarrier →ₗ.[ℝ] ConcreteL2R1HilbertCarrier
  pmapDomain : pmap.domain = concreteL2R2DiagonalDomainCandidateSubmodule
  pmapDenseDomain : Dense ((pmap.domain : Set ConcreteL2R1HilbertCarrier))
  pmapGraphEqDenseGraph :
    ((pmap.graph : Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier)
  pmapGraphEqCompletedGraph :
    ((pmap.graph : Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2CompletedDiagonalGraphCarrier)
  pmapGraphEqFormalAdjointGraph :
    ((pmap.graph : Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph)
  pmapIsClosed : LinearPMap.IsClosed pmap
  boundaryNotAdjointEquality : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete LinearPMap promotion surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapSurface :=
  { actualAdjointPromotionObligationReady :=
      concrete_l2_r2_dense_diagonal_domain_actual_adjoint_promotion_obligation_ready
    pmap := concreteL2R2DenseDiagonalDomainLinearPMap
    pmapDomain := concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain
    pmapDenseDomain := concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain
    pmapGraphEqDenseGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_dense_graph_carrier
    pmapGraphEqCompletedGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier
    pmapGraphEqFormalAdjointGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_formal_adjoint_linear_map_graph
    pmapIsClosed := concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    boundaryNotAdjointEquality := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the dense-domain LinearPMap surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady : Prop :=
  concreteL2R2DenseDiagonalDomainActualAdjointPromotionObligation ∧
  Dense ((concreteL2R2DenseDiagonalDomainLinearPMap.domain : Set ConcreteL2R1HilbertCarrier)) ∧
  ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
      Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier) ∧
  ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
      Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
    concreteL2R2CompletedDiagonalGraphCarrier) ∧
  ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
      Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSurface.boundaryNotAdjointEquality ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSurface.boundaryNotSelfAdjointness

/-- The dense-domain LinearPMap surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_actual_adjoint_promotion_obligation_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_dense_graph_carrier,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_formal_adjoint_linear_map_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    trivial,
    trivial⟩

/-- Boundary marker: the concrete diagonal operator is now represented as an
actual Mathlib `LinearPMap` with dense domain and closed graph.  The remaining
boundary is the equality with Mathlib's `adjoint` and hence `IsSelfAdjoint`. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady

/-- Boundary theorem for the dense-domain LinearPMap surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_surface_ready

end

end MathlibAnalytic
end MGAP4D
