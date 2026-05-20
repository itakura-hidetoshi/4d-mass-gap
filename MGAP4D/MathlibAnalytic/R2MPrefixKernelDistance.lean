import MGAP4D.MathlibAnalytic.R2MPrefixBoundedSeminormSurface

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Negation on the explicit bounded-prefix graph-pair carrier, expressed using
its scalar surface.  This intentionally avoids introducing global typeclass
instances before the quotient/normed-carrier boundary is constructed. -/
def concreteL2GraphPairPrefixEnergyBoundedNeg
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    ConcreteL2GraphPairPrefixEnergyBoundedElement :=
  concreteL2GraphPairPrefixEnergyBoundedSmul (-1 : ℝ) x

/-- Subtraction on the explicit bounded-prefix graph-pair carrier. -/
def concreteL2GraphPairPrefixEnergyBoundedSub
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    ConcreteL2GraphPairPrefixEnergyBoundedElement :=
  concreteL2GraphPairPrefixEnergyBoundedAdd x
    (concreteL2GraphPairPrefixEnergyBoundedNeg y)

/-- Finite-prefix pseudo-distance induced by the bounded seminorm candidate. -/
def r2mPrefixPseudoDistance
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) : ℝ :=
  concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
    (concreteL2GraphPairPrefixEnergyBoundedSub x y)

/-- The bounded negation operation is scalar multiplication by `-1`. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_neg_eq_smul
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedNeg x =
      concreteL2GraphPairPrefixEnergyBoundedSmul (-1 : ℝ) x := by
  rfl

/-- Inner product against a bounded negation in the left argument. -/
theorem r2m_prefix_inner_neg_left
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N
        (concreteL2GraphPairPrefixEnergyBoundedNeg x) y =
      - concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left]
  ring

/-- Inner product against a bounded negation in the right argument. -/
theorem r2m_prefix_inner_neg_right
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x
        (concreteL2GraphPairPrefixEnergyBoundedNeg y) =
      - concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_right]
  ring

/-- The quadratic functional is invariant under bounded negation. -/
theorem r2m_prefix_quadratic_neg_eq
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedNeg x) =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq]
  ring

/-- The self-difference has zero finite-prefix quadratic energy.  This is the
kernel-reflexivity lemma needed before quotienting by the zero-kernel. -/
theorem r2m_prefix_quadratic_sub_self_eq_zero
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub x x) = 0 := by
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion]
  rw [r2m_prefix_inner_neg_right]
  rw [r2m_prefix_quadratic_neg_eq]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_self_eq_quadratic]
  ring

/-- The finite-prefix pseudo-distance from a point to itself is zero. -/
theorem r2m_prefix_pseudo_distance_self
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N x x = 0 := by
  unfold r2mPrefixPseudoDistance
  unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
  rw [r2m_prefix_quadratic_sub_self_eq_zero]
  exact Real.sqrt_zero

/-- Nonnegativity of the finite-prefix pseudo-distance. -/
theorem r2m_prefix_pseudo_distance_nonneg
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    0 ≤ r2mPrefixPseudoDistance N x y := by
  unfold r2mPrefixPseudoDistance
  exact concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg N
    (concreteL2GraphPairPrefixEnergyBoundedSub x y)

/-- Kernel-distance readiness package: the explicit subtractive surface is now
available and the self-distance vanishes, but symmetry/transitivity/quotient
transport are still kept as visible next obligations. -/
def r2mPrefixKernelDistanceReady : Prop :=
  (∀ x : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    concreteL2GraphPairPrefixEnergyBoundedNeg x =
      concreteL2GraphPairPrefixEnergyBoundedSmul (-1 : ℝ) x) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub x x) = 0) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixPseudoDistance N x x = 0) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ r2mPrefixPseudoDistance N x y)

/-- The kernel-distance surface is ready up to the self-zero pseudo-distance
law. -/
theorem r2m_prefix_kernel_distance_ready :
    r2mPrefixKernelDistanceReady := by
  exact ⟨
    concrete_l2_graph_pair_prefix_energy_bounded_neg_eq_smul,
    r2m_prefix_quadratic_sub_self_eq_zero,
    r2m_prefix_pseudo_distance_self,
    r2m_prefix_pseudo_distance_nonneg⟩

/-- Boundary marker for the next quotient step. -/
def r2mPrefixKernelQuotientBoundaryHeld : Prop :=
  r2mPrefixKernelDistanceReady ∧
  True  -- quotient construction and transport remain the next layer

theorem r2m_prefix_kernel_quotient_boundary_held :
    r2mPrefixKernelQuotientBoundaryHeld := by
  exact ⟨r2m_prefix_kernel_distance_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
