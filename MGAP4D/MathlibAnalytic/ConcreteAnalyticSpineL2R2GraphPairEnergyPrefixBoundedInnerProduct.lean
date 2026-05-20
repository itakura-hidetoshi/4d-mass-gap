import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite-prefix real inner-product candidate on bounded-prefix graph-pair
elements.  This is the finite dot product associated to the two coordinates
of the concrete graph pair. -/
def concreteL2GraphPairPrefixEnergyBoundedInnerProduct
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) : ℝ :=
  (Finset.range N).sum fun n =>
    (concreteL2GraphPairFst x.1).1 n * (concreteL2GraphPairFst y.1).1 n +
      (concreteL2GraphPairSnd x.1).1 n * (concreteL2GraphPairSnd y.1).1 n

/-- Self inner-product recovers the bounded finite-prefix quadratic functional. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_self_eq_quadratic
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x x =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  unfold concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional
  unfold concreteL2GraphPairEnergyPrefix
  unfold concreteL2GraphPairEnergyTerm
  exact Finset.sum_congr rfl fun n _hn => by
    ring

/-- Symmetry of the bounded finite-prefix inner-product candidate. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_symm
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y x := by
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  exact Finset.sum_congr rfl fun n _hn => by
    ring

/-- The bounded finite-prefix inner-product candidate vanishes on zero in the
left argument. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_left
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
        concreteL2GraphPairPrefixEnergyBoundedZero x = 0 := by
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  exact Finset.sum_eq_zero fun n _hn => by
    simp [concrete_l2_graph_pair_prefix_energy_bounded_zero_val,
      concreteL2GraphPairZero, concreteL2GraphPairFst, concreteL2GraphPairSnd,
      concreteL2RealZero]

/-- The bounded finite-prefix inner-product candidate vanishes on zero in the
right argument. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_right
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
        concreteL2GraphPairPrefixEnergyBoundedZero = 0 := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm]
  exact concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_left N x

/-- Left additivity of the bounded finite-prefix inner-product candidate. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_add_left
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) z =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z +
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y z := by
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _hn => by
    simp [concreteL2GraphPairPrefixEnergyBoundedAdd, concreteL2GraphPairAdd,
      concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealAdd]
    ring

/-- Right additivity follows from symmetry and left additivity. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_add_right
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
        (concreteL2GraphPairPrefixEnergyBoundedAdd y z) =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y +
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N x
    (concreteL2GraphPairPrefixEnergyBoundedAdd y z)]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_add_left]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N y x]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N z x]

/-- Left scalar law of the bounded finite-prefix inner-product candidate. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left
    (N : ℕ) (c : ℝ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y =
      c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _hn => by
    simp [concreteL2GraphPairPrefixEnergyBoundedSmul, concreteL2GraphPairSmul,
      concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealSmul]
    ring

/-- Right scalar law follows from symmetry and left scalar law. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_right
    (N : ℕ) (c : ℝ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
        (concreteL2GraphPairPrefixEnergyBoundedSmul c y) =
      c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N x
    (concreteL2GraphPairPrefixEnergyBoundedSmul c y)]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N y x]

/-- R2ah bounded finite-prefix inner-product surface.  This packages the finite
dot product, its link to the quadratic functional, and its elementary bilinear
laws.  It remains below the Cauchy--Schwarz/Minkowski/triangle layer. -/
structure ConcreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface where
  r2agReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeReady
  innerProduct : ℕ → ConcreteL2GraphPairPrefixEnergyBoundedElement →
    ConcreteL2GraphPairPrefixEnergyBoundedElement → ℝ
  innerSelfQuadratic : ∀ (N : ℕ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N x x = concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x
  innerSymm : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N x y = innerProduct N y x
  innerZeroLeft : ∀ (N : ℕ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N concreteL2GraphPairPrefixEnergyBoundedZero x = 0
  innerZeroRight : ∀ (N : ℕ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N x concreteL2GraphPairPrefixEnergyBoundedZero = 0
  innerAddLeft : ∀ (N : ℕ)
      (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N (concreteL2GraphPairPrefixEnergyBoundedAdd x y) z =
      innerProduct N x z + innerProduct N y z
  innerAddRight : ∀ (N : ℕ)
      (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N x (concreteL2GraphPairPrefixEnergyBoundedAdd y z) =
      innerProduct N x y + innerProduct N x z
  innerSmulLeft : ∀ (N : ℕ) (c : ℝ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y =
      c * innerProduct N x y
  innerSmulRight : ∀ (N : ℕ) (c : ℝ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    innerProduct N x (concreteL2GraphPairPrefixEnergyBoundedSmul c y) =
      c * innerProduct N x y
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

/-- Concrete R2ah bounded finite-prefix inner-product surface. -/
def concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface :
    ConcreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface :=
  { r2agReady :=
      concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_triangle_bridge_ready
    innerProduct := concreteL2GraphPairPrefixEnergyBoundedInnerProduct
    innerSelfQuadratic :=
      concrete_l2_graph_pair_prefix_energy_bounded_inner_self_eq_quadratic
    innerSymm := concrete_l2_graph_pair_prefix_energy_bounded_inner_symm
    innerZeroLeft := concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_left
    innerZeroRight := concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_right
    innerAddLeft := concrete_l2_graph_pair_prefix_energy_bounded_inner_add_left
    innerAddRight := concrete_l2_graph_pair_prefix_energy_bounded_inner_add_right
    innerSmulLeft := concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left
    innerSmulRight := concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_right
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

/-- R2ah readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedTriangleBridgeReady ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x x =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y x) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
      concreteL2GraphPairPrefixEnergyBoundedZero x = 0) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
      concreteL2GraphPairPrefixEnergyBoundedZero = 0) ∧
  (∀ (N : ℕ) (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
      (concreteL2GraphPairPrefixEnergyBoundedAdd x y) z =
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z +
          concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y z) ∧
  (∀ (N : ℕ) (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
      (concreteL2GraphPairPrefixEnergyBoundedAdd y z) =
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y +
          concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z) ∧
  (∀ (N : ℕ) (c : ℝ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
      (concreteL2GraphPairPrefixEnergyBoundedSmul c x) y =
        c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y) ∧
  (∀ (N : ℕ) (c : ℝ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
      (concreteL2GraphPairPrefixEnergyBoundedSmul c y) =
        c * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y) ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotCauchySchwarz ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotMinkowskiSquare ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotTriangleInequalityInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotSeminormInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotNormedSpaceInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixBoundedInnerProductSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2ah. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_inner_product_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_triangle_bridge_ready <|
      And.intro
        concrete_l2_graph_pair_prefix_energy_bounded_inner_self_eq_quadratic <|
        And.intro
          concrete_l2_graph_pair_prefix_energy_bounded_inner_symm <|
          And.intro
            concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_left <|
            And.intro
              concrete_l2_graph_pair_prefix_energy_bounded_inner_zero_right <|
              And.intro
                concrete_l2_graph_pair_prefix_energy_bounded_inner_add_left <|
                And.intro
                  concrete_l2_graph_pair_prefix_energy_bounded_inner_add_right <|
                  And.intro
                    concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left <|
                    And.intro
                      concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_right <|
                      And.intro trivial <| And.intro trivial <| And.intro trivial <|
                        And.intro trivial <| And.intro trivial <| And.intro trivial <|
                          And.intro trivial <| And.intro trivial <|
                            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2ah. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductReady

/-- Boundary theorem for R2ah. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_inner_product_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProductHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_inner_product_ready

end

end MathlibAnalytic
end MGAP4D
