import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTrianglePreSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Root-two additive bound for the graph-norm candidate.

The current completed-energy add-control gives the coarse pre-triangle estimate
`candidate(p + q) ≤ sqrt(2 candidate(p)^2 + 2 candidate(q)^2)`.  This lemma
turns it into a more familiar additive bound with constant `sqrt 2`.

This is still weaker than the true triangle inequality and does not claim a
normed structure or topology.
-/
theorem concrete_l2_graph_norm_candidate_add_le_root_two_sum
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      Real.sqrt (2 : ℝ) *
        (concreteL2GraphNormCandidate p + concreteL2GraphNormCandidate q) := by
  let a := concreteL2GraphNormCandidate p
  let b := concreteL2GraphNormCandidate q
  have ha : 0 ≤ a := by
    dsimp [a]
    exact concrete_l2_graph_norm_candidate_nonneg p
  have hb : 0 ≤ b := by
    dsimp [b]
    exact concrete_l2_graph_norm_candidate_nonneg q
  have hsum_nonneg : 0 ≤ a + b := add_nonneg ha hb
  have hB_nonneg :
      0 ≤ (2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hcoarse :
      concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
        Real.sqrt ((2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2) := by
    dsimp [a, b]
    exact concrete_l2_graph_norm_candidate_add_le_sqrt_bound p q
  have hrad_le :
      (2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2 ≤
        (2 : ℝ) * (a + b) ^ 2 := by
    nlinarith [mul_nonneg ha hb]
  have hsqrt_le :
      Real.sqrt ((2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2) ≤
        Real.sqrt ((2 : ℝ) * (a + b) ^ 2) := by
    exact Real.sqrt_le_sqrt hrad_le
  have hroot_expand :
      Real.sqrt ((2 : ℝ) * (a + b) ^ 2) =
        Real.sqrt (2 : ℝ) * (a + b) := by
    rw [Real.sqrt_mul]
    · rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg hsum_nonneg]
    · norm_num
  exact le_trans hcoarse (le_trans hsqrt_le (le_of_eq hroot_expand))

/-- Root-two additive bound package for the graph-norm candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBound : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      Real.sqrt (2 : ℝ) *
        (concreteL2GraphNormCandidate p + concreteL2GraphNormCandidate q)

/-- The root-two additive bound package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_root_two_add_bound :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBound := by
  exact concrete_l2_graph_norm_candidate_add_le_root_two_sum

/--
Root-two pre-triangle surface.

This records that the candidate is a homogeneous, nonnegative, zero-at-zero
seminorm-like gauge up to a `sqrt 2` quasi-triangle constant.  The exact
triangle inequality remains downstream.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBoundSurface where
  preTriangleReady : concreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurfaceReady
  rootTwoAddBound : concreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBound
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete root-two pre-triangle surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBoundSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBoundSurface :=
  { preTriangleReady :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_triangle_pre_surface_ready
    rootTwoAddBound :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_root_two_add_bound
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True
    boundaryNotCore := True }

/-- Readiness predicate for the root-two pre-triangle surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBoundSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBound

/-- Readiness theorem for the root-two pre-triangle surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_root_two_add_bound_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateRootTwoAddBoundSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_triangle_pre_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_root_two_add_bound⟩

end

end MathlibAnalytic
end MGAP4D
