import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansion

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_nonneg
    (N : ℕ) (c : ℝ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y) := by
  exact concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg N _

theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_expansion
    (N : ℕ) (c : ℝ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y) =
      (c ^ 2) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) *
          (c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y) +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left]

structure ConcreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface where
  r2aiReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady
  quadraticPolynomialNonneg : ∀ (N : ℕ) (c : ℝ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y)
  quadraticPolynomialExpansion : ∀ (N : ℕ) (c : ℝ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y) =
      (c ^ 2) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) *
          (c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y) +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y
  boundaryNotCauchySchwarz : Prop
  boundaryNotMinkowskiSquare : Prop
  boundaryNotTriangleInequalityInstance : Prop
  boundaryNotSeminormInstance : Prop
  boundaryNotNormedSpaceInstance : Prop

def concreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface :
    ConcreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface :=
  { r2aiReady :=
      concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready
    quadraticPolynomialNonneg :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_nonneg
    quadraticPolynomialExpansion :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_expansion
    boundaryNotCauchySchwarz := True
    boundaryNotMinkowskiSquare := True
    boundaryNotTriangleInequalityInstance := True
    boundaryNotSeminormInstance := True
    boundaryNotNormedSpaceInstance := True }

def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady ∧
  (∀ (N : ℕ) (c : ℝ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y)) ∧
  (∀ (N : ℕ) (c : ℝ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y) =
      (c ^ 2) • concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) *
          (c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y) +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface.boundaryNotCauchySchwarz ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface.boundaryNotMinkowskiSquare ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface.boundaryNotTriangleInequalityInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface.boundaryNotSeminormInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialSurface.boundaryNotNormedSpaceInstance

theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_polynomial_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready,
    concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_nonneg,
    concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_expansion,
    trivial, trivial, trivial, trivial, trivial⟩

def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialReady

theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_polynomial_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomialHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_polynomial_ready

end

end MathlibAnalytic
end MGAP4D
