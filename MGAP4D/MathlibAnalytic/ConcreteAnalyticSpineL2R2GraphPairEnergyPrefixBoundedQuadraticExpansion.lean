import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProduct

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Quadratic expansion for the bounded finite-prefix quadratic functional.
This is the finite-prefix parallelogram-facing identity
`Q(x+y) = Q(x) + 2⟪x,y⟫ + Q(y)`, proved directly by `Finset` algebra and
`ring_nf`. -/
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
    Finset.sum_add_distrib, Finset.sum_mul]
  ring_nf

/-- Polarization form of the bounded finite-prefix quadratic expansion.  This
keeps the Cauchy--Schwarz/Minkowski bridge in a form that can be reused by the
next layer without reopening the coordinate algebra. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_polarization_from_add
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y) -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  have h :=
    concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion N x y
  rw [h]
  ring

/-- The quadratic expansion is symmetric in the cross term, by symmetry of the
finite-prefix inner-product candidate. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion_symm_cross
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x +
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y x +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N y x]
  exact concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion N x y

/-- R2ai bounded finite-prefix quadratic expansion surface.  It closes the
coordinate expansion layer and prepares the Cauchy--Schwarz/Minkowski layer,
without yet asserting Cauchy--Schwarz, triangle inequality, or any seminorm
instance. -/
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

/-- Concrete R2ai bounded finite-prefix quadratic expansion surface. -/
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

/-- R2ai readiness. -/
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

/-- Readiness theorem for R2ai. -/
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

/-- Boundary marker for R2ai. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionReady

/-- Boundary theorem for R2ai. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_quadratic_expansion_ready

end

end MathlibAnalytic
end MGAP4D
