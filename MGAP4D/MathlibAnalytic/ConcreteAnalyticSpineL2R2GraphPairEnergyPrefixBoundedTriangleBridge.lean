import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneity

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The square-level obligation needed to promote the bounded finite-prefix
seminorm candidate to a triangle inequality statement.  It is deliberately an
obligation, not asserted globally in this file. -/
def concreteL2GraphPairPrefixEnergyBoundedTriangleSquareObligation
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) : Prop :=
  concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
      (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ^ 2 ≤
    (concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x +
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y) ^ 2

/-- The triangle inequality statement for the bounded finite-prefix seminorm
candidate.  This remains a target statement until the square obligation is
proved from a finite-dimensional Cauchy--Schwarz/Minkowski argument. -/
def concreteL2GraphPairPrefixEnergyBoundedTriangleInequality
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) : Prop :=
  concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
      (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x +
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y

/-- Square-to-triangle bridge for the bounded finite-prefix seminorm candidate.
This is the real-analysis promotion step: once the stronger square estimate
`‖x+y‖² ≤ (‖x‖+‖y‖)²` is available, mathlib's `sq_le_sq`, together with
nonnegativity and `abs_of_nonneg`, gives the triangle inequality. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_triangle_from_square_obligation
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hsq : concreteL2GraphPairPrefixEnergyBoundedTriangleSquareObligation N x y) :
    concreteL2GraphPairPrefixEnergyBoundedTriangleInequality N x y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedTriangleSquareObligation at hsq
  unfold concreteL2GraphPairPrefixEnergyBoundedTriangleInequality
  have hleft_nonneg :
      0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) :=
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg N
      (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
  have hx_nonneg :
      0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x :=
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg N x
  have hy_nonneg :
      0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y :=
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg N y
  have hright_nonneg :
      0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x +
        concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y := by
    exact add_nonneg hx_nonneg hy_nonneg
  have habs := (sq_le_sq.mp hsq)
  rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs

/-- R2ag bounded finite-prefix triangle bridge surface.  It proves only the
mathlib real-analysis bridge from a square obligation to triangle inequality;
it does not yet provide the missing finite-prefix Cauchy--Schwarz/Minkowski
square obligation itself. -/
structure ConcreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface where
  r2afReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityReady
  triangleSquareObligation :
    ℕ → ConcreteL2GraphPairPrefixEnergyBoundedElement →
      ConcreteL2GraphPairPrefixEnergyBoundedElement → Prop
  triangleInequality :
    ℕ → ConcreteL2GraphPairPrefixEnergyBoundedElement →
      ConcreteL2GraphPairPrefixEnergyBoundedElement → Prop
  triangleFromSquareObligation : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    triangleSquareObligation N x y → triangleInequality N x y
  boundarySquareObligationNotYetClosed : Prop
  boundaryNotTriangleInequalityInstance : Prop
  boundaryNotSeminormInstance : Prop
  boundaryNotNormedSpaceInstance : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2ag bounded finite-prefix triangle bridge surface. -/
def concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface :
    ConcreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface :=
  { r2afReady :=
      concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_absolute_homogeneity_ready
    triangleSquareObligation :=
      concreteL2GraphPairPrefixEnergyBoundedTriangleSquareObligation
    triangleInequality :=
      concreteL2GraphPairPrefixEnergyBoundedTriangleInequality
    triangleFromSquareObligation :=
      concrete_l2_graph_pair_prefix_energy_bounded_triangle_from_square_obligation
    boundarySquareObligationNotYetClosed := True
    boundaryNotTriangleInequalityInstance := True
    boundaryNotSeminormInstance := True
    boundaryNotNormedSpaceInstance := True
    boundaryNotGraphNormTopology := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2ag readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityReady ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedTriangleSquareObligation N x y →
      concreteL2GraphPairPrefixEnergyBoundedTriangleInequality N x y) ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundarySquareObligationNotYetClosed ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotTriangleInequalityInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotSeminormInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotNormedSpaceInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixBoundedTriangleBridgeSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2ag. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_triangle_bridge_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_absolute_homogeneity_ready <|
      And.intro
        concrete_l2_graph_pair_prefix_energy_bounded_triangle_from_square_obligation <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2ag. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeReady

/-- Boundary theorem for R2ag. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_triangle_bridge_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_triangle_bridge_ready

end

end MathlibAnalytic
end MGAP4D
