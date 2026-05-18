import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalGraphNorm

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-support core inside the concrete l2 diagonal domain.  This is a core
carrier surface only: it is not yet a density theorem, not graph closure, not a
closed-operator theorem, and not self-adjointness. -/
def ConcreteL2DiagonalFiniteSupportDomainCarrier : Type :=
  { x : ConcreteL2DiagonalDomainCarrier // ConcreteL2RealFiniteSupport x.1 }

/-- The zero domain point belongs to the finite-support core. -/
def concreteL2DiagonalFiniteSupportDomainZero :
    ConcreteL2DiagonalFiniteSupportDomainCarrier :=
  ⟨concreteL2DiagonalDomainZero, concrete_l2_real_zero_finite_support⟩

/-- The finite-support core is nonempty. -/
theorem concrete_l2_diagonal_finite_support_domain_nonempty :
    Nonempty ConcreteL2DiagonalFiniteSupportDomainCarrier := by
  exact ⟨concreteL2DiagonalFiniteSupportDomainZero⟩

/-- The finite-support core is included in the diagonal domain by construction. -/
def concreteL2FiniteSupportCoreToDomain
    (x : ConcreteL2DiagonalFiniteSupportDomainCarrier) :
    ConcreteL2DiagonalDomainCarrier :=
  x.1

/-- The finite-support core action is the l2-valued diagonal action restricted
to the finite-support domain carrier. -/
def concreteL2FiniteSupportCoreActionL2
    (x : ConcreteL2DiagonalFiniteSupportDomainCarrier) : ConcreteL2RealSequence :=
  concreteL2DiagonalActionL2 x.1

/-- The finite-support core action sends the zero core point to the zero carrier
point extensionally. -/
theorem concrete_l2_finite_support_core_action_zero_ext (n : ℕ) :
    (concreteL2FiniteSupportCoreActionL2
      concreteL2DiagonalFiniteSupportDomainZero).1 n = concreteL2RealZero.1 n := by
  exact concrete_l2_diagonal_action_l2_zero_ext n

/-- Graph carrier for the finite-support core action. -/
def ConcreteL2FiniteSupportCoreGraphCarrier :
    Set (ConcreteL2RealSequence × ConcreteL2RealSequence) :=
  {p | ∃ x : ConcreteL2DiagonalFiniteSupportDomainCarrier,
    p = (x.1.1, concreteL2FiniteSupportCoreActionL2 x)}

/-- Pair equality for the zero point in the finite-support core graph. -/
theorem concrete_l2_finite_support_core_zero_graph_pair_eq :
    (concreteL2RealZero, concreteL2RealZero) =
      (concreteL2DiagonalFiniteSupportDomainZero.1.1,
        concreteL2FiniteSupportCoreActionL2
          concreteL2DiagonalFiniteSupportDomainZero) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext n
    exact (concrete_l2_finite_support_core_action_zero_ext n).symm

/-- The finite-support core graph is nonempty. -/
theorem concrete_l2_finite_support_core_graph_nonempty :
    ConcreteL2FiniteSupportCoreGraphCarrier.Nonempty := by
  refine ⟨(concreteL2RealZero, concreteL2RealZero), ?_⟩
  refine ⟨concreteL2DiagonalFiniteSupportDomainZero, ?_⟩
  exact concrete_l2_finite_support_core_zero_graph_pair_eq

/-- Zero graph point membership in the finite-support core graph. -/
theorem concrete_l2_finite_support_core_zero_graph_mem :
    (concreteL2RealZero, concreteL2RealZero) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier := by
  refine ⟨concreteL2DiagonalFiniteSupportDomainZero, ?_⟩
  exact concrete_l2_finite_support_core_zero_graph_pair_eq

/-- Surface for the finite-support core lane.  This records a concrete core
inside the diagonal domain but does not yet assert density or essential
self-adjointness. -/
structure ConcreteL2FiniteSupportCoreSurface where
  coreCarrier : Type
  coreNonempty : Nonempty coreCarrier
  coreGraphCarrier : Set (ConcreteL2RealSequence × ConcreteL2RealSequence)
  coreGraphNonempty : coreGraphCarrier.Nonempty
  zeroCoreGraphMem : (concreteL2RealZero, concreteL2RealZero) ∈ coreGraphCarrier
  boundaryNotDensityTheorem : Prop
  boundaryNotEssentialSelfAdjointness : Prop
  boundaryNotClosedOperatorTheorem : Prop

/-- The concrete finite-support core surface. -/
def concreteL2FiniteSupportCoreSurface : ConcreteL2FiniteSupportCoreSurface :=
  { coreCarrier := ConcreteL2DiagonalFiniteSupportDomainCarrier
    coreNonempty := concrete_l2_diagonal_finite_support_domain_nonempty
    coreGraphCarrier := ConcreteL2FiniteSupportCoreGraphCarrier
    coreGraphNonempty := concrete_l2_finite_support_core_graph_nonempty
    zeroCoreGraphMem := concrete_l2_finite_support_core_zero_graph_mem
    boundaryNotDensityTheorem := True
    boundaryNotEssentialSelfAdjointness := True
    boundaryNotClosedOperatorTheorem := True }

/-- Readiness for the finite-support core surface. -/
def concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady : Prop :=
  concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady ∧
  Nonempty ConcreteL2DiagonalFiniteSupportDomainCarrier ∧
  concreteL2FiniteSupportCoreSurface.coreGraphCarrier.Nonempty ∧
  concreteL2FiniteSupportCoreSurface.boundaryNotDensityTheorem ∧
  concreteL2FiniteSupportCoreSurface.boundaryNotEssentialSelfAdjointness ∧
  concreteL2FiniteSupportCoreSurface.boundaryNotClosedOperatorTheorem

/-- Readiness theorem for the finite-support core surface. -/
theorem concrete_analytic_spine_l2_finite_support_core_surface_ready :
    concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady := by
  unfold concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady
  exact And.intro concrete_analytic_spine_l2_diagonal_graph_norm_surface_ready <|
    And.intro concrete_l2_diagonal_finite_support_domain_nonempty <|
      And.intro concrete_l2_finite_support_core_graph_nonempty <|
        And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the finite-support core surface. -/
def concreteAnalyticSpineL2FiniteSupportCoreHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady

/-- Boundary theorem for the finite-support core surface. -/
theorem concrete_analytic_spine_l2_finite_support_core_hard_residual_boundary_held :
    concreteAnalyticSpineL2FiniteSupportCoreHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_finite_support_core_surface_ready

end

end MathlibAnalytic
end MGAP4D
