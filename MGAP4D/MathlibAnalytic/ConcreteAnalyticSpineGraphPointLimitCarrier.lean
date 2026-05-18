import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphPointLimitSequence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A graph-point limit carrier surface records that a concrete graph-limit point
lies in a chosen carrier.  It is only a limit-carrier bookkeeping surface.  It is
not a graph closure theorem, not a graph-norm completion theorem, not a Cauchy
completion theorem, not a closed-operator theorem, not self-adjointness, and not
an R3 promotion. -/
structure ConcreteGraphPointLimitCarrierSurface
    (T : ConcreteDenseDomainOperator) where
  graphLimitWitness : ConcreteGraphLimitWitness T
  limitCarrier : Set (ConcreteRealHilbertSpace × ConcreteRealHilbertSpace)
  limitPointMemCarrier : graphLimitWitness.limitPoint ∈ limitCarrier
  limitCarrierBoundaryNotClosureTheorem : Prop

/-- The toy identity graph-limit point `(0,0)` lies in the identity diagonal
carrier. -/
theorem concrete_identity_graph_limit_point_mem_diagonal_carrier :
    concreteIdentityGraphLimitWitness.limitPoint ∈
      concreteIdentityGraphDiagonalCarrier := by
  simp [concreteIdentityGraphLimitWitness, concreteIdentityGraphDiagonalCarrier]

/-- The identity graph-limit witness has a concrete limit-carrier surface.  This
does not assert graph closure, graph-norm completion, Cauchy completion,
closedness, self-adjointness, a spectral theorem, a PVM, or any `33/20` atom. -/
def concreteIdentityGraphPointLimitCarrierSurface :
    ConcreteGraphPointLimitCarrierSurface concreteIdentityDenseDomainOperator :=
  { graphLimitWitness := concreteIdentityGraphLimitWitness
    limitCarrier := concreteIdentityGraphDiagonalCarrier
    limitPointMemCarrier := concrete_identity_graph_limit_point_mem_diagonal_carrier
    limitCarrierBoundaryNotClosureTheorem := True }

/-- The graph-point limit-carrier surface keeps the closure/completion boundary
closed. -/
theorem concrete_identity_graph_point_limit_carrier_boundary :
    concreteIdentityGraphPointLimitCarrierSurface.limitCarrierBoundaryNotClosureTheorem := by
  trivial

/-- R2 graph-point-limit-carrier readiness for the from-scratch concrete analytic
spine.  This records that the toy graph-limit point lies in the diagonal carrier
while staying below graph closure, graph-norm completion, Cauchy completion,
closed-operator status, and R3. -/
def concreteAnalyticSpineR2GraphPointLimitCarrierSurfaceReady : Prop :=
  concreteAnalyticSpineR2GraphPointLimitSequenceSurfaceReady ∧
  concreteIdentityGraphLimitWitness.limitPoint ∈
    concreteIdentityGraphDiagonalCarrier ∧
  concreteIdentityGraphPointLimitCarrierSurface.limitCarrierBoundaryNotClosureTheorem

/-- R2 graph-point-limit-carrier readiness for the from-scratch concrete analytic
spine. -/
theorem concrete_analytic_spine_r2_graph_point_limit_carrier_surface_ready :
    concreteAnalyticSpineR2GraphPointLimitCarrierSurfaceReady := by
  unfold concreteAnalyticSpineR2GraphPointLimitCarrierSurfaceReady
  exact And.intro concrete_analytic_spine_r2_graph_point_limit_sequence_surface_ready <|
    And.intro concrete_identity_graph_limit_point_mem_diagonal_carrier
      concrete_identity_graph_point_limit_carrier_boundary

/-- Boundary marker: the graph-point limit-carrier surface has not discharged
graph closure, graph-norm completion, Cauchy completion, the physical nonbounded
Hamiltonian, closedness, self-adjointness, PVM, plaquette observable,
non-definitional `33/20` emergence, or positive spectral-weight derivation. -/
def concreteAnalyticSpineR2GraphPointLimitCarrierHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineR2GraphPointLimitCarrierSurfaceReady

/-- Boundary theorem for the R2 graph-point-limit-carrier addendum. -/
theorem concrete_analytic_spine_r2_graph_point_limit_carrier_hard_residual_boundary_held :
    concreteAnalyticSpineR2GraphPointLimitCarrierHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_r2_graph_point_limit_carrier_surface_ready

end

end MathlibAnalytic
end MGAP4D
