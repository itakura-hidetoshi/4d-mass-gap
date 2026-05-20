import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Extensionality for bounded-prefix graph-pair elements.  This exposes the
standard mathlib `Subtype.ext` interface so later files can reason by the
underlying concrete graph pair. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_ext
    {x y : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (h : x.1 = y.1) : x = y := by
  exact Subtype.ext h

/-- The bounded zero element projects to the concrete graph-pair zero. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_zero_val :
    concreteL2GraphPairPrefixEnergyBoundedZero.1 = concreteL2GraphPairZero := by
  rfl

/-- The bounded addition operation projects to concrete graph-pair addition. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_val
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    (concreteL2GraphPairPrefixEnergyBoundedAdd x y).1 =
      concreteL2GraphPairAdd x.1 y.1 := by
  rfl

/-- The bounded scalar operation projects to concrete graph-pair scalar
multiplication. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_val
    (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    (concreteL2GraphPairPrefixEnergyBoundedSmul c x).1 =
      concreteL2GraphPairSmul c x.1 := by
  rfl

/-- Finite-prefix additive energy estimate restricted to bounded-prefix carrier
elements. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_energy_le
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y).1 ≤
      (2 : ℝ) • concreteL2GraphPairEnergyPrefix N x.1 +
        (2 : ℝ) • concreteL2GraphPairEnergyPrefix N y.1 := by
  simpa [concrete_l2_graph_pair_prefix_energy_bounded_add_val] using
    concrete_l2_graph_pair_energy_prefix_add_le_prefix_bound N x.1 y.1

/-- Finite-prefix scalar energy law restricted to bounded-prefix carrier
elements. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_energy_eq
    (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x).1 =
      (c ^ 2) • concreteL2GraphPairEnergyPrefix N x.1 := by
  simpa [concrete_l2_graph_pair_prefix_energy_bounded_smul_val] using
    concrete_l2_graph_pair_energy_prefix_smul_eq_prefix_smul N c x.1

/-- Every bounded-prefix element carries a finite-prefix bound witness. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_has_bound
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    ∃ B : ℝ, ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N x.1 ≤ B := by
  exact x.2

/-- R2ac readiness: bounded-prefix elements expose a mathlib-friendly subtype
API and carry the finite-prefix add/smul energy laws. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearSurfaceReady ∧
  (∀ {x y : ConcreteL2GraphPairPrefixEnergyBoundedElement},
    x.1 = y.1 → x = y) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y).1 ≤
      (2 : ℝ) • concreteL2GraphPairEnergyPrefix N x.1 +
        (2 : ℝ) • concreteL2GraphPairEnergyPrefix N y.1) ∧
  (∀ (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x).1 =
      (c ^ 2) • concreteL2GraphPairEnergyPrefix N x.1) ∧
  (∀ x : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    ∃ B : ℝ, ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N x.1 ≤ B)

/-- Readiness theorem for R2ac. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_element_api_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_linear_surface_ready <|
      And.intro
        (fun h => concrete_l2_graph_pair_prefix_energy_bounded_ext h) <|
        And.intro
          concrete_l2_graph_pair_prefix_energy_bounded_add_energy_le <|
          And.intro
            concrete_l2_graph_pair_prefix_energy_bounded_smul_energy_eq
            concrete_l2_graph_pair_prefix_energy_bounded_has_bound

/-- Boundary marker for R2ac. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIReady

/-- Boundary theorem for R2ac. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_element_api_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedElementAPIHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_element_api_ready

end

end MathlibAnalytic
end MGAP4D
