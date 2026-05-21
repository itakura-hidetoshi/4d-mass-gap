import MGAP4D.MathlibAnalytic.R2MPrefixKernelDistance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Inner-product expansion for bounded subtraction in the left argument. -/
theorem r2m_prefix_inner_sub_left
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
        (concreteL2GraphPairPrefixEnergyBoundedSub x y) z =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z -
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y z := by
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_add_left]
  rw [r2m_prefix_inner_neg_left]
  ring

/-- Inner-product expansion for bounded subtraction in the right argument. -/
theorem r2m_prefix_inner_sub_right
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
        (concreteL2GraphPairPrefixEnergyBoundedSub y z) =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y -
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z := by
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_add_right]
  rw [r2m_prefix_inner_neg_right]
  ring

/-- Quadratic expansion for a bounded difference. -/
theorem r2m_prefix_quadratic_sub_expansion
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x -
        (2 : ℝ) * concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y +
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion]
  rw [r2m_prefix_inner_neg_right]
  rw [r2m_prefix_quadratic_neg_eq]
  ring

/-- Symmetry of the finite-prefix quadratic difference. -/
theorem r2m_prefix_quadratic_sub_symm
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub x y) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub y x) := by
  rw [r2m_prefix_quadratic_sub_expansion N x y]
  rw [r2m_prefix_quadratic_sub_expansion N y x]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N y x]
  ring

/-- Symmetry of the finite-prefix pseudo-distance. -/
theorem r2m_prefix_pseudo_distance_symm
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N x y = r2mPrefixPseudoDistance N y x := by
  unfold r2mPrefixPseudoDistance
  unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
  rw [r2m_prefix_quadratic_sub_symm N x y]

/-- Inner product of two bounded differences, expanded purely through the
finite-prefix bilinear surface. -/
theorem r2m_prefix_inner_sub_sub
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
        (concreteL2GraphPairPrefixEnergyBoundedSub x y)
        (concreteL2GraphPairPrefixEnergyBoundedSub y z) =
      concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y -
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x z -
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y +
        concreteL2GraphPairPrefixEnergyBoundedInnerProduct N y z := by
  rw [r2m_prefix_inner_sub_left]
  rw [r2m_prefix_inner_sub_right]
  rw [r2m_prefix_inner_sub_right]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_self_eq_quadratic]
  ring

/-- Quadratic consistency of the telescoping difference
`(x-y)+(y-z)` with `x-z`.  This is deliberately stated at quadratic level,
so no additive-group typeclass instance is needed on the explicit carrier. -/
theorem r2m_prefix_quadratic_sub_add_sub_eq_sub
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd
          (concreteL2GraphPairPrefixEnergyBoundedSub x y)
          (concreteL2GraphPairPrefixEnergyBoundedSub y z)) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub x z) := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion]
  rw [r2m_prefix_quadratic_sub_expansion N x y]
  rw [r2m_prefix_quadratic_sub_expansion N y z]
  rw [r2m_prefix_inner_sub_sub N x y z]
  rw [r2m_prefix_quadratic_sub_expansion N x z]
  ring

/-- Triangle inequality for the finite-prefix pseudo-distance induced by the
bounded seminorm candidate. -/
theorem r2m_prefix_pseudo_distance_triangle
    (N : ℕ)
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N x z ≤
      r2mPrefixPseudoDistance N x y + r2mPrefixPseudoDistance N y z := by
  unfold r2mPrefixPseudoDistance
  have hleft :
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
          (concreteL2GraphPairPrefixEnergyBoundedSub x z) =
        concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
          (concreteL2GraphPairPrefixEnergyBoundedAdd
            (concreteL2GraphPairPrefixEnergyBoundedSub x y)
            (concreteL2GraphPairPrefixEnergyBoundedSub y z)) := by
    unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
    rw [← r2m_prefix_quadratic_sub_add_sub_eq_sub N x y z]
  rw [hleft]
  exact r2m_prefix_triangle_inequality N
    (concreteL2GraphPairPrefixEnergyBoundedSub x y)
    (concreteL2GraphPairPrefixEnergyBoundedSub y z)

/-- The finite-prefix pseudo-distance package now has nonnegativity,
self-zero, symmetry, and triangle.  It remains a pseudo-metric surface rather
than a quotient metric because distinct points may have zero finite-prefix
separation. -/
def r2mPrefixPseudoMetricReady : Prop :=
  r2mPrefixKernelDistanceReady ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixPseudoDistance N x y = r2mPrefixPseudoDistance N y x) ∧
  (∀ (N : ℕ) (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixPseudoDistance N x z ≤
      r2mPrefixPseudoDistance N x y + r2mPrefixPseudoDistance N y z)

/-- Readiness theorem for the finite-prefix pseudo-metric surface. -/
theorem r2m_prefix_pseudo_metric_ready :
    r2mPrefixPseudoMetricReady := by
  exact ⟨
    r2m_prefix_kernel_distance_ready,
    r2m_prefix_pseudo_distance_symm,
    r2m_prefix_pseudo_distance_triangle⟩

/-- Boundary marker: the next step is quotienting the zero-distance relation. -/
def r2mPrefixPseudoMetricQuotientBoundaryHeld : Prop :=
  r2mPrefixPseudoMetricReady ∧
  True

theorem r2m_prefix_pseudo_metric_quotient_boundary_held :
    r2mPrefixPseudoMetricQuotientBoundaryHeld := by
  exact ⟨r2m_prefix_pseudo_metric_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
