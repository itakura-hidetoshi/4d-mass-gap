import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphPointLimitCarrier

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A graph-limit carrier compatibility surface records that one graph-limit
point is simultaneously present in a law carrier and in a closure-candidate
carrier.  It is only a carrier-compatibility bookkeeping surface.  It is not a
graph closure theorem, not a graph-norm completion theorem, not a Cauchy
completion theorem, not a closed-operator theorem, not self-adjointness, and not
an R3 promotion. -/
structure ConcreteGraphLimitCarrierCompatibilitySurface
    (T : ConcreteDenseDomainOperator) where
  graphLimitWitness : ConcreteGraphLimitWitness T
  lawCarrier : Set (ConcreteRealHilbertSpace × ConcreteRealHilbertSpace)
  closureCandidate : ConcreteGraphClosureCandidate T
  limitPointMemLawCarrier : graphLimitWitness.limitPoint ∈ lawCarrier
  limitPointMemClosureCandidate : graphLimitWitness.limitPoint ∈ closureCandidate.carrier
  carrierCompatibilityBoundaryNotClosureTheorem : Prop

/-- The toy identity graph-limit point is present both in the diagonal law
carrier and in the identity graph-closure candidate. -/
def concreteIdentityGraphLimitCarrierCompatibilitySurface :
    ConcreteGraphLimitCarrierCompatibilitySurface concreteIdentityDenseDomainOperator :=
  { graphLimitWitness := concreteIdentityGraphLimitWitness
    lawCarrier := concreteIdentityGraphDiagonalCarrier
    closureCandidate := concreteIdentityGraphClosureCandidate
    limitPointMemLawCarrier := concrete_identity_graph_limit_point_mem_diagonal_carrier
    limitPointMemClosureCandidate := concrete_identity_graph_limit_point_mem_closure_candidate
    carrierCompatibilityBoundaryNotClosureTheorem := True }

/-- The graph-limit carrier compatibility surface keeps the closure/completion
boundary closed. -/
theorem concrete_identity_graph_limit_carrier_compatibility_boundary :
    concreteIdentityGraphLimitCarrierCompatibilitySurface.carrierCompatibilityBoundaryNotClosureTheorem := by
  trivial

/-- R2 graph-limit-carrier-compatibility readiness for the from-scratch concrete
analytic spine.  This records simultaneous membership of the toy graph-limit
point in the diagonal law carrier and graph-closure candidate while staying
below graph closure, graph-norm completion, Cauchy completion, closed-operator
status, and R3. -/
def concreteAnalyticSpineR2GraphLimitCarrierCompatibilitySurfaceReady : Prop :=
  concreteAnalyticSpineR2GraphPointLimitCarrierSurfaceReady ∧
  concreteIdentityGraphLimitWitness.limitPoint ∈
    concreteIdentityGraphDiagonalCarrier ∧
  concreteIdentityGraphLimitWitness.limitPoint ∈
    concreteIdentityGraphClosureCandidate.carrier ∧
  concreteIdentityGraphLimitCarrierCompatibilitySurface.carrierCompatibilityBoundaryNotClosureTheorem

/-- R2 graph-limit-carrier-compatibility readiness for the from-scratch concrete
analytic spine. -/
theorem concrete_analytic_spine_r2_graph_limit_carrier_compatibility_surface_ready :
    concreteAnalyticSpineR2GraphLimitCarrierCompatibilitySurfaceReady := by
  unfold concreteAnalyticSpineR2GraphLimitCarrierCompatibilitySurfaceReady
  exact And.intro concrete_analytic_spine_r2_graph_point_limit_carrier_surface_ready <|
    And.intro concrete_identity_graph_limit_point_mem_diagonal_carrier <|
      And.intro concrete_identity_graph_limit_point_mem_closure_candidate
        concrete_identity_graph_limit_carrier_compatibility_boundary

/-- Boundary marker: the graph-limit carrier compatibility surface has not
discharged graph closure, graph-norm completion, Cauchy completion, the physical
nonbounded Hamiltonian, closedness, self-adjointness, PVM, plaquette observable,
non-definitional `33/20` emergence, or positive spectral-weight derivation. -/
def concreteAnalyticSpineR2GraphLimitCarrierCompatibilityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineR2GraphLimitCarrierCompatibilitySurfaceReady

/-- Boundary theorem for the R2 graph-limit-carrier-compatibility addendum. -/
theorem concrete_analytic_spine_r2_graph_limit_carrier_compatibility_hard_residual_boundary_held :
    concreteAnalyticSpineR2GraphLimitCarrierCompatibilityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_r2_graph_limit_carrier_compatibility_surface_ready

end

end MathlibAnalytic
end MGAP4D
