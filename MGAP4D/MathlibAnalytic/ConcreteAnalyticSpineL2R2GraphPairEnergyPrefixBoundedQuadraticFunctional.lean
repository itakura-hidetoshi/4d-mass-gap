import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPI

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite-prefix quadratic functional on bounded-prefix graph-pair elements.
This is the bounded-element presentation of `concreteL2GraphPairEnergyPrefix`.
It is deliberately a quadratic functional surface, not yet a norm or seminorm
instance. -/
def concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) : ℝ :=
  concreteL2GraphPairEnergyPrefix N x.1

/-- The bounded finite-prefix quadratic functional is nonnegative. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
  exact concrete_l2_graph_pair_energy_prefix_nonneg N x.1

/-- The bounded finite-prefix quadratic functional vanishes at zero. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_zero
    (N : ℕ) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        concreteL2GraphPairPrefixEnergyBoundedZero = 0 := by
  exact concrete_l2_graph_pair_energy_prefix_zero N

/-- Additive quadratic upper bound on bounded-prefix elements.  This is the
finite-prefix energy estimate transported through the bounded subtype API. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_le
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      (2 : ℝ) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  exact concrete_l2_graph_pair_prefix_energy_bounded_add_energy_le N x y

/-- Scalar quadratic law on bounded-prefix elements. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq
    (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      (c ^ 2) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
  exact concrete_l2_graph_pair_prefix_energy_bounded_smul_energy_eq N c x

/-- Each bounded-prefix element has a uniform finite-prefix quadratic bound. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_has_bound
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    ∃ B : ℝ, ∀ N : ℕ,
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x ≤ B := by
  exact concrete_l2_graph_pair_prefix_energy_bounded_has_bound x

/-- R2ad bounded quadratic functional surface.  This packages the finite-prefix
quadratic functional on the bounded carrier with nonnegativity, zero, additive
upper bound, scalar law, and boundedness witnesses.  It intentionally does not
claim a normed vector-space instance, triangle inequality for a square root,
completion, closed operator, self-adjointness, spectral theorem, PVM, or
positive spectral weight. -/
structure ConcreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface where
  r2acReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIReady
  quadraticFunctional : ℕ → ConcreteL2GraphPairPrefixEnergyBoundedElement → ℝ
  quadraticNonneg : ∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ quadraticFunctional N x
  quadraticZero : ∀ N : ℕ,
    quadraticFunctional N concreteL2GraphPairPrefixEnergyBoundedZero = 0
  quadraticAddBound : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    quadraticFunctional N (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      (2 : ℝ) • quadraticFunctional N x +
        (2 : ℝ) • quadraticFunctional N y
  quadraticSmulLaw : ∀ (N : ℕ) (c : ℝ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    quadraticFunctional N (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      (c ^ 2) • quadraticFunctional N x
  quadraticBoundWitness : ∀ x : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    ∃ B : ℝ, ∀ N : ℕ, quadraticFunctional N x ≤ B
  boundaryNotSeminormInstance : Prop
  boundaryNotNormedSpaceInstance : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2ad bounded quadratic functional surface. -/
def concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface :
    ConcreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface :=
  { r2acReady :=
      concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_element_api_ready
    quadraticFunctional := concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional
    quadraticNonneg :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg
    quadraticZero := concrete_l2_graph_pair_prefix_energy_bounded_quadratic_zero
    quadraticAddBound :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_le
    quadraticSmulLaw :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq
    quadraticBoundWitness :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_has_bound
    boundaryNotSeminormInstance := True
    boundaryNotNormedSpaceInstance := True
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2ad readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIReady ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) ∧
  (∀ N : ℕ,
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      concreteL2GraphPairPrefixEnergyBoundedZero = 0) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      (2 : ℝ) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) ∧
  (∀ (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      (c ^ 2) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) ∧
  (∀ x : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    ∃ B : ℝ, ∀ N : ℕ,
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x ≤ B) ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotSeminormInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotNormedSpaceInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2ad. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_functional_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_element_api_ready <|
      And.intro
        concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg <|
        And.intro
          concrete_l2_graph_pair_prefix_energy_bounded_quadratic_zero <|
          And.intro
            concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_le <|
            And.intro
              concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq <|
              And.intro
                concrete_l2_graph_pair_prefix_energy_bounded_quadratic_has_bound <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial <| And.intro trivial <| And.intro trivial <|
                    And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2ad. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalReady

/-- Boundary theorem for R2ad. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_functional_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticFunctionalHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_functional_ready

end

end MathlibAnalytic
end MGAP4D
