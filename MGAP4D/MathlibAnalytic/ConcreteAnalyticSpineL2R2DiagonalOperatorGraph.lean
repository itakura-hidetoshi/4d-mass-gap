import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalDomainAdditiveClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- R2f diagonal-operator domain as a subtype of the completed real `ℓ²`
carrier.  This is the first layer where the dense domain is packaged as an
actual domain type. -/
abbrev ConcreteL2R2DiagonalOperatorDomain : Type :=
  {x : ConcreteL2R1HilbertCarrier // ConcreteL2R2DiagonalDomainCandidate x}

/-- Coercion from the diagonal-operator domain to the ambient completed carrier. -/
def concreteL2R2DiagonalOperatorDomainCarrier
    (x : ConcreteL2R2DiagonalOperatorDomain) : ConcreteL2R1HilbertCarrier :=
  x.1

/-- Domain membership carried by a point of the diagonal-operator domain. -/
theorem concrete_l2_r2_diagonal_operator_domain_mem
    (x : ConcreteL2R2DiagonalOperatorDomain) :
    ConcreteL2R2DiagonalDomainCandidate x.1 :=
  x.2

/-- The zero vector as a point of the diagonal-operator domain. -/
def concreteL2R2DiagonalOperatorDomainZero :
    ConcreteL2R2DiagonalOperatorDomain :=
  ⟨concreteL2R1HilbertZero, concrete_l2_r2_diagonal_domain_candidate_zero⟩

/-- The diagonal graph relation: `y` is the diagonal image of `x` iff all
coordinates of `y` are the weighted coordinates of `x`.

This is deliberately a graph relation, not yet a bundled closed/self-adjoint
operator. -/
def concreteL2R2DiagonalOperatorGraph
    (x : ConcreteL2R2DiagonalOperatorDomain)
    (y : ConcreteL2R1HilbertCarrier) : Prop :=
  ∀ n : ℕ, y n = concreteL2R2WeightedCoordinate x.1 n

/-- The graph relation is functional at the coordinate level: two graph outputs
with the same domain input have the same coordinates. -/
theorem concrete_l2_r2_diagonal_operator_graph_coordinate_unique
    (x : ConcreteL2R2DiagonalOperatorDomain)
    {y z : ConcreteL2R1HilbertCarrier}
    (hy : concreteL2R2DiagonalOperatorGraph x y)
    (hz : concreteL2R2DiagonalOperatorGraph x z)
    (n : ℕ) :
    y n = z n := by
  rw [hy n, hz n]

/-- Graph output for zero has all coordinates zero. -/
theorem concrete_l2_r2_diagonal_operator_graph_zero_coordinates
    {y : ConcreteL2R1HilbertCarrier}
    (hy : concreteL2R2DiagonalOperatorGraph
      concreteL2R2DiagonalOperatorDomainZero y)
    (n : ℕ) :
    y n = 0 := by
  rw [hy n]
  simp [concreteL2R2WeightedCoordinate, concreteL2R2DiagonalOperatorDomainZero,
    concrete_l2_r1_hilbert_zero_apply]

/-- Dense-domain witness inherited from R2e: the diagonal-domain candidate is
dense in the ambient completed carrier. -/
theorem concrete_l2_r2_diagonal_operator_domain_dense_target :
    concreteL2R2DiagonalDomainCandidateDenseTarget :=
  concrete_l2_r2_diagonal_domain_candidate_dense_target_ready

/-- Closure form of the dense-domain witness for the diagonal-operator domain. -/
theorem concrete_l2_r2_diagonal_operator_domain_closure_eq_univ :
    concreteL2R2DiagonalDomainCandidateClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier) :=
  concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ

/-- Adapter predicate for the R2f diagonal-operator graph surface. -/
def concreteL2R2DiagonalOperatorGraphAdapter : Prop :=
  Nonempty ConcreteL2R2DiagonalOperatorDomain ∧
  concreteL2R2DiagonalDomainCandidateDenseTarget ∧
  (∀ x : ConcreteL2R2DiagonalOperatorDomain,
    ConcreteL2R2DiagonalDomainCandidate x.1) ∧
  (∀ (x : ConcreteL2R2DiagonalOperatorDomain)
      {y z : ConcreteL2R1HilbertCarrier},
    concreteL2R2DiagonalOperatorGraph x y →
    concreteL2R2DiagonalOperatorGraph x z →
    ∀ n : ℕ, y n = z n)

/-- Adapter theorem for the R2f diagonal-operator graph surface. -/
theorem concrete_l2_r2_diagonal_operator_graph_adapter_ready :
    concreteL2R2DiagonalOperatorGraphAdapter := by
  exact ⟨
    ⟨concreteL2R2DiagonalOperatorDomainZero⟩,
    concrete_l2_r2_diagonal_operator_domain_dense_target,
    concrete_l2_r2_diagonal_operator_domain_mem,
    by
      intro x y z hy hz n
      exact concrete_l2_r2_diagonal_operator_graph_coordinate_unique x hy hz n⟩

/-- R2f diagonal-operator graph surface.

This packages the dense domain as a subtype and introduces the diagonal graph
relation.  It intentionally does not yet claim that the raw coordinate formula
has been bundled as a closed operator, nor does it assert unboundedness,
self-adjointness, spectral theorem application, PVM construction, or positive
spectral weight. -/
structure ConcreteL2R2DiagonalOperatorGraphSurface where
  additiveClosureReady : concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady
  domain : Type
  carrier : domain → ConcreteL2R1HilbertCarrier
  graph : domain → ConcreteL2R1HilbertCarrier → Prop
  domainNonempty : Nonempty domain
  denseDomainTarget : concreteL2R2DiagonalDomainCandidateDenseTarget
  domainClosureEqUniv :
    concreteL2R2DiagonalDomainCandidateClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier)
  coordinateUniqueness :
    ∀ (x : ConcreteL2R2DiagonalOperatorDomain)
      {y z : ConcreteL2R1HilbertCarrier},
      concreteL2R2DiagonalOperatorGraph x y →
      concreteL2R2DiagonalOperatorGraph x z →
      ∀ n : ℕ, y n = z n
  boundaryNotOperatorBundled : Prop
  boundaryNotUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2f diagonal-operator graph surface. -/
def concreteL2R2DiagonalOperatorGraphSurface :
    ConcreteL2R2DiagonalOperatorGraphSurface :=
  { additiveClosureReady :=
      concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready
    domain := ConcreteL2R2DiagonalOperatorDomain
    carrier := concreteL2R2DiagonalOperatorDomainCarrier
    graph := concreteL2R2DiagonalOperatorGraph
    domainNonempty := ⟨concreteL2R2DiagonalOperatorDomainZero⟩
    denseDomainTarget := concrete_l2_r2_diagonal_operator_domain_dense_target
    domainClosureEqUniv := concrete_l2_r2_diagonal_operator_domain_closure_eq_univ
    coordinateUniqueness :=
      by
        intro x y z hy hz n
        exact concrete_l2_r2_diagonal_operator_graph_coordinate_unique x hy hz n
    boundaryNotOperatorBundled := True
    boundaryNotUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2f diagonal-operator graph readiness. -/
def concreteAnalyticSpineL2R2DiagonalOperatorGraphSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady ∧
  concreteL2R2DiagonalOperatorGraphAdapter ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotOperatorBundled ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotUnboundednessTheorem ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotPVMConstruction ∧
  concreteL2R2DiagonalOperatorGraphSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2f. -/
theorem concrete_analytic_spine_l2_r2_diagonal_operator_graph_surface_ready :
    concreteAnalyticSpineL2R2DiagonalOperatorGraphSurfaceReady := by
  unfold concreteAnalyticSpineL2R2DiagonalOperatorGraphSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready <|
      And.intro concrete_l2_r2_diagonal_operator_graph_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2f diagonal-operator graph surface. -/
def concreteAnalyticSpineL2R2DiagonalOperatorGraphHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DiagonalOperatorGraphSurfaceReady

/-- Boundary theorem for the R2f diagonal-operator graph surface. -/
theorem concrete_analytic_spine_l2_r2_diagonal_operator_graph_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DiagonalOperatorGraphHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_diagonal_operator_graph_surface_ready

end

end MathlibAnalytic
end MGAP4D
