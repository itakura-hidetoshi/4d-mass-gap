import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalGraph

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The diagonal raw action as an `l2` carrier-valued action.  The domain proof is
exactly the square-summability witness for the weighted sequence. -/
def concreteL2DiagonalActionL2 (x : ConcreteL2DiagonalDomainCarrier) :
    ConcreteL2RealSequence :=
  ⟨concreteL2DiagonalRawAction x, by
    simpa [concreteL2DiagonalRawAction, ConcreteL2DiagonalDomain, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using x.2⟩

/-- The `l2`-valued diagonal action sends the zero domain point to the zero
carrier point extensionally. -/
theorem concrete_l2_diagonal_action_l2_zero_ext (n : ℕ) :
    (concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero).1 n =
      concreteL2RealZero.1 n := by
  simp [concreteL2DiagonalActionL2, concreteL2DiagonalRawAction,
    concreteL2DiagonalDomainZero, concreteL2RealZero]

/-- Pair equality for the zero point in the `l2` graph carrier. -/
theorem concrete_l2_diagonal_zero_graph_l2_pair_eq :
    (concreteL2RealZero, concreteL2RealZero) =
      (concreteL2DiagonalDomainZero.1,
        concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext n
    exact (concrete_l2_diagonal_action_l2_zero_ext n).symm

/-- Graph carrier with both coordinates in the concrete `l2` carrier. -/
def ConcreteL2DiagonalGraphL2Carrier :
    Set (ConcreteL2RealSequence × ConcreteL2RealSequence) :=
  {p | ∃ x : ConcreteL2DiagonalDomainCarrier,
    p = (x.1, concreteL2DiagonalActionL2 x)}

/-- The `l2` graph carrier is nonempty via the zero domain point. -/
theorem concrete_l2_diagonal_graph_l2_carrier_nonempty :
    ConcreteL2DiagonalGraphL2Carrier.Nonempty := by
  refine ⟨(concreteL2RealZero, concreteL2RealZero), ?_⟩
  refine ⟨concreteL2DiagonalDomainZero, ?_⟩
  exact concrete_l2_diagonal_zero_graph_l2_pair_eq

/-- Zero graph point membership in the `l2` graph carrier. -/
theorem concrete_l2_diagonal_zero_graph_l2_point_mem :
    (concreteL2RealZero, concreteL2RealZero) ∈ ConcreteL2DiagonalGraphL2Carrier := by
  refine ⟨concreteL2DiagonalDomainZero, ?_⟩
  exact concrete_l2_diagonal_zero_graph_l2_pair_eq

/-- A graph-norm skeleton for the concrete `l2` diagonal action. -/
structure ConcreteL2DiagonalGraphNormSurface where
  graphL2Carrier : Set (ConcreteL2RealSequence × ConcreteL2RealSequence)
  graphL2CarrierNonempty : graphL2Carrier.Nonempty
  zeroGraphL2PointMem : (concreteL2RealZero, concreteL2RealZero) ∈ graphL2Carrier
  boundaryNotGraphNormCompletion : Prop
  boundaryNotClosedOperatorTheorem : Prop

/-- The concrete `l2` diagonal graph-norm skeleton surface. -/
def concreteL2DiagonalGraphNormSurface : ConcreteL2DiagonalGraphNormSurface :=
  { graphL2Carrier := ConcreteL2DiagonalGraphL2Carrier
    graphL2CarrierNonempty := concrete_l2_diagonal_graph_l2_carrier_nonempty
    zeroGraphL2PointMem := concrete_l2_diagonal_zero_graph_l2_point_mem
    boundaryNotGraphNormCompletion := True
    boundaryNotClosedOperatorTheorem := True }

/-- Readiness for the concrete `l2` diagonal graph-norm skeleton. -/
def concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady : Prop :=
  concreteAnalyticSpineL2DiagonalGraphSurfaceReady ∧
  ConcreteL2DiagonalGraphL2Carrier.Nonempty ∧
  True ∧ True

/-- Readiness theorem for the concrete `l2` diagonal graph-norm skeleton. -/
theorem concrete_analytic_spine_l2_diagonal_graph_norm_surface_ready :
    concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady := by
  unfold concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady
  exact And.intro concrete_analytic_spine_l2_diagonal_graph_surface_ready <|
    And.intro concrete_l2_diagonal_graph_l2_carrier_nonempty <|
      And.intro trivial trivial

/-- Boundary marker for the concrete `l2` diagonal graph-norm skeleton. -/
def concreteAnalyticSpineL2DiagonalGraphNormHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady

/-- Boundary theorem for the concrete `l2` diagonal graph-norm skeleton. -/
theorem concrete_analytic_spine_l2_diagonal_graph_norm_hard_residual_boundary_held :
    concreteAnalyticSpineL2DiagonalGraphNormHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_diagonal_graph_norm_surface_ready

end

end MathlibAnalytic
end MGAP4D
