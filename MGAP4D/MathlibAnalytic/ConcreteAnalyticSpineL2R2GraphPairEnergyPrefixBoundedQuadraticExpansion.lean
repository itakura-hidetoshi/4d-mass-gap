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
    (fun n => x.1.1 n) (fun n => y.1.1 n)]
  rw [concrete_l2_graph_pair_prefix_sum_sq_add_expansion N
    (fun n => x.1.2 n) (fun n => y.1.2 n)]
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

structure ConcreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface where
  r2ahReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductReady
  quadraticAddExpansion : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y
  polarizationFromAdd : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y) -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y
  quadraticAddExpansionSymmCross : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y x +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y
  boundaryNotCauchySchwarz : Prop
  boundaryNotMinkowskiSquare : Prop
  boundaryNotTriangleInequalityInstance : Prop
  boundaryNotSeminormInstance : Prop
  boundaryNotNormedSpaceInstance : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

def concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface :
    ConcreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface :=
  { r2ahReady :=
      concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_inner_product_ready
    quadraticAddExpansion :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion
    polarizationFromAdd :=
      concrete_l2_graph_pair_prefix_energy_bounded_polarization_from_add
    quadraticAddExpansionSymmCross :=
      concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion_symm_cross
    boundaryNotCauchySchwarz := True
    boundaryNotMinkowskiSquare := True
    boundaryNotTriangleInequalityInstance := True
    boundaryNotSeminormInstance := True
    boundaryNotNormedSpaceInstance := True
    boundaryNotGraphNormTopology := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

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
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotCauchySchwarz ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotMinkowskiSquare ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotTriangleInequalityInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotSeminormInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotNormedSpaceInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionSurface.boundaryNotPositiveSpectralWeight

theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_inner_product_ready <|
      And.intro
        concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion <|
        And.intro
          concrete_l2_graph_pair_prefix_energy_bounded_polarization_from_add <|
          And.intro
            concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion_symm_cross <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial trivial

def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady

theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready

end

end MathlibAnalytic
end MGAP4D
