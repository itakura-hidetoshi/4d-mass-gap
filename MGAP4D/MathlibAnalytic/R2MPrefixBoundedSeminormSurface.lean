import MGAP4D.MathlibAnalytic.R2MPrefixTriangleInequality
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- User-facing square-root triangle form for the finite-prefix quadratic
energy.  This is the direct Minkowski inequality
`√(Q_N (x + y)) ≤ √(Q_N x) + √(Q_N y)`, obtained by unfolding the already
proved seminorm-candidate triangle inequality. -/
theorem r2m_prefix_sqrt_quadratic_triangle
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    Real.sqrt
        (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y)) ≤
      Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) +
        Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) := by
  simpa [concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate] using
    r2m_prefix_triangle_inequality N x y

/-- The finite-prefix bounded energy seminorm-candidate laws, stated without
promoting to a Mathlib `Seminorm` or quotient instance.  The carrier here is
still the concrete bounded graph-pair surface with explicit zero/add/smul
operations, so this surface records the laws at the current API boundary. -/
def r2mPrefixBoundedSeminormCandidateLawReady : Prop :=
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ∧
  (∀ N : ℕ,
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
      concreteL2GraphPairPrefixEnergyBoundedZero = 0) ∧
  (∀ (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      |c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x +
        concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x ^ 2 =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    Real.sqrt
        (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y)) ≤
      Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) +
        Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y))

/-- The R2m finite-prefix bounded graph-pair energy surface now has the full
seminorm-candidate law package: nonnegativity, zero, absolute homogeneity,
triangle inequality, square recovery, and the unfolded square-root triangle
form. -/
theorem r2m_prefix_bounded_seminorm_candidate_law_ready :
    r2mPrefixBoundedSeminormCandidateLawReady := by
  exact ⟨
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg,
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_zero,
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs,
    r2m_prefix_triangle_inequality,
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq,
    r2m_prefix_sqrt_quadratic_triangle⟩

/-- Post-triangle R2m surface.  It deliberately stops below quotienting by the
zero-kernel and below Mathlib typeclass promotion.  This keeps the next proof
obligation visible: construct the kernel quotient, then transport this
candidate to a genuine seminormed/normed carrier. -/
structure R2MPrefixBoundedSeminormSurface where
  candidate : ℕ → ConcreteL2GraphPairPrefixEnergyBoundedElement → ℝ
  candidateNonneg : ∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ candidate N x
  candidateZero : ∀ N : ℕ,
    candidate N concreteL2GraphPairPrefixEnergyBoundedZero = 0
  candidateSmulAbs : ∀ (N : ℕ) (c : ℝ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    candidate N (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      |c| * candidate N x
  candidateTriangle : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    candidate N (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      candidate N x + candidate N y
  candidateSquareRecovery : ∀ (N : ℕ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    candidate N x ^ 2 =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x
  sqrtQuadraticTriangle : ∀ (N : ℕ)
      (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    Real.sqrt
        (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedAdd x y)) ≤
      Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) +
        Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y)
  boundaryNotKernelQuotientConstructed : Prop
  boundaryNotSeminormTypeclassInstance : Prop
  boundaryNotNormedAddCommGroupInstance : Prop
  boundaryNotHilbertCompletion : Prop
  boundaryNotClosedOperatorPromotion : Prop

/-- Concrete post-triangle R2m seminorm-candidate surface. -/
def r2mPrefixBoundedSeminormSurface : R2MPrefixBoundedSeminormSurface :=
  { candidate := concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
    candidateNonneg :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg
    candidateZero :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_zero
    candidateSmulAbs :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs
    candidateTriangle := r2m_prefix_triangle_inequality
    candidateSquareRecovery :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq
    sqrtQuadraticTriangle := r2m_prefix_sqrt_quadratic_triangle
    boundaryNotKernelQuotientConstructed := True
    boundaryNotSeminormTypeclassInstance := True
    boundaryNotNormedAddCommGroupInstance := True
    boundaryNotHilbertCompletion := True
    boundaryNotClosedOperatorPromotion := True }

/-- Boundary marker for the post-triangle finite-prefix seminorm surface. -/
def r2mPrefixBoundedSeminormSurfaceReady : Prop :=
  r2mPrefixBoundedSeminormCandidateLawReady ∧
  r2mPrefixBoundedSeminormSurface.boundaryNotKernelQuotientConstructed ∧
  r2mPrefixBoundedSeminormSurface.boundaryNotSeminormTypeclassInstance ∧
  r2mPrefixBoundedSeminormSurface.boundaryNotNormedAddCommGroupInstance ∧
  r2mPrefixBoundedSeminormSurface.boundaryNotHilbertCompletion ∧
  r2mPrefixBoundedSeminormSurface.boundaryNotClosedOperatorPromotion

theorem r2m_prefix_bounded_seminorm_surface_ready :
    r2mPrefixBoundedSeminormSurfaceReady := by
  exact ⟨
    r2m_prefix_bounded_seminorm_candidate_law_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
