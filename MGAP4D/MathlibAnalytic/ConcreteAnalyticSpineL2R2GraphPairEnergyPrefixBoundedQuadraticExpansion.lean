import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedFiniteSumSquare

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional
  unfold concreteL2GraphPairEnergyPrefix
  unfold concreteL2GraphPairEnergyTerm
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  simp [concreteL2GraphPairPrefixEnergyBoundedAdd, concreteL2GraphPairAdd,
    concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealAdd,
    Finset.sum_add_distrib]
  rw [concrete_l2_graph_pair_prefix_sum_sq_add_expansion N
    (fun n => x.1.1.1 n) (fun n => y.1.1.1 n)]
  rw [concrete_l2_graph_pair_prefix_sum_sq_add_expansion N
    (fun n => x.1.2.1 n) (fun n => y.1.2.1 n)]
  ring

theorem concrete_l2_graph_pair_prefix_energy_bounded_polarization_from_add
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y) -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion N x y]
  ring

theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion_symm_cross
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y x +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N y x]
  exact concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion N x y

def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductReady ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y) -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y x +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y)

theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_inner_product_ready,
    concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion,
    concrete_l2_graph_pair_prefix_energy_bounded_polarization_from_add,
    concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion_symm_cross⟩

def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady

theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready

end

end MathlibAnalytic
end MGAP4D
