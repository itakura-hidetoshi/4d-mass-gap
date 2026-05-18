import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2RealSequence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Graph carrier for the concrete l2 diagonal raw action.  This is a graph of
the domain carrier into raw real sequences, not yet a closed graph theorem. -/
def ConcreteL2DiagonalGraphCarrier :
    Set (ConcreteL2RealSequence × (ℕ → ℝ)) :=
  {p | ∃ x : ConcreteL2DiagonalDomainCarrier,
    p = (x.1, concreteL2DiagonalRawAction x)}

/-- The l2 diagonal graph carrier is nonempty via the zero domain point. -/
theorem concrete_l2_diagonal_graph_carrier_nonempty :
    ConcreteL2DiagonalGraphCarrier.Nonempty := by
  refine ⟨(concreteL2RealZero, fun _ => 0), ?_⟩
  refine ⟨concreteL2DiagonalDomainZero, ?_⟩
  ext n
  · rfl
  · simp [concreteL2DiagonalRawAction, concreteL2DiagonalDomainZero,
      concreteL2RealZero]

/-- The zero graph point lies in the l2 diagonal graph carrier. -/
theorem concrete_l2_diagonal_zero_graph_point_mem :
    (concreteL2RealZero, fun _ : ℕ => 0) ∈ ConcreteL2DiagonalGraphCarrier := by
  refine ⟨concreteL2DiagonalDomainZero, ?_⟩
  ext n
  · rfl
  · simp [concreteL2DiagonalRawAction, concreteL2DiagonalDomainZero,
      concreteL2RealZero]

/-- A graph surface for the l2 diagonal raw action.  This is R2 graph data only:
not a graph closure theorem, not a closed-operator theorem, and not
self-adjointness. -/
structure ConcreteL2DiagonalGraphSurface where
  graphCarrier : Set (ConcreteL2RealSequence × (ℕ → ℝ))
  graphCarrierNonempty : graphCarrier.Nonempty
  zeroGraphPointMem : (concreteL2RealZero, fun _ : ℕ => 0) ∈ graphCarrier
  boundaryNotClosedOperatorTheorem : Prop

/-- The concrete l2 diagonal graph surface. -/
def concreteL2DiagonalGraphSurface : ConcreteL2DiagonalGraphSurface :=
  { graphCarrier := ConcreteL2DiagonalGraphCarrier
    graphCarrierNonempty := concrete_l2_diagonal_graph_carrier_nonempty
    zeroGraphPointMem := concrete_l2_diagonal_zero_graph_point_mem
    boundaryNotClosedOperatorTheorem := True }

/-- Readiness for the concrete l2 diagonal graph surface. -/
def concreteAnalyticSpineL2DiagonalGraphSurfaceReady : Prop :=
  concreteAnalyticSpineL2RealCarrierSurfaceReady ∧
  concreteL2DiagonalGraphSurface.graphCarrier.Nonempty ∧
  concreteL2DiagonalGraphSurface.boundaryNotClosedOperatorTheorem

/-- Readiness theorem for the concrete l2 diagonal graph surface. -/
theorem concrete_analytic_spine_l2_diagonal_graph_surface_ready :
    concreteAnalyticSpineL2DiagonalGraphSurfaceReady := by
  unfold concreteAnalyticSpineL2DiagonalGraphSurfaceReady
  exact And.intro concrete_analytic_spine_l2_real_carrier_surface_ready <|
    And.intro concrete_l2_diagonal_graph_carrier_nonempty trivial

/-- Boundary marker for the concrete l2 diagonal graph surface. -/
def concreteAnalyticSpineL2DiagonalGraphHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2DiagonalGraphSurfaceReady

/-- Boundary theorem for the concrete l2 diagonal graph surface. -/
theorem concrete_analytic_spine_l2_diagonal_graph_hard_residual_boundary_held :
    concreteAnalyticSpineL2DiagonalGraphHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_diagonal_graph_surface_ready

end

end MathlibAnalytic
end MGAP4D
