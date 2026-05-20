import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticPolynomial

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

def concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) : ℝ :=
  - concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y /
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x

theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_vertex_nonneg
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul
          (concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff N x y) x) y) := by
  exact concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_nonneg
    N (concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff N x y) x y

theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_vertex_expansion
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
      (concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul
          (concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff N x y) x) y) =
      (concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff N x y ^ 2) •
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) *
          (concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff N x y *
            concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y) +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  exact concrete_l2_graph_pair_prefix_energy_bounded_quadratic_polynomial_expansion
    N (concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff N x y) x y

end

end MathlibAnalytic
end MGAP4D
