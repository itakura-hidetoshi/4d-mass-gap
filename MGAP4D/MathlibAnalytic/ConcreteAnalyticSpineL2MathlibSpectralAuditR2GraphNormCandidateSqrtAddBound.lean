import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Sqrt-form add-control for the graph-norm candidate.

This is the direct candidate-level inequality obtained from the squared
add-bound.  It is still weaker than the true triangle inequality, but it is now
an upper bound for the candidate itself rather than only for its square.
-/
theorem concrete_l2_graph_norm_candidate_add_le_sqrt_bound
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      Real.sqrt
        ((2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
          (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2) := by
  let a := concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q)
  let B := (2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
    (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    exact concrete_l2_graph_norm_candidate_nonneg (concreteL2GraphPairAdd p q)
  have hB : 0 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg (concreteL2GraphNormCandidate p),
      sq_nonneg (concreteL2GraphNormCandidate q)]
  have hsquare : a ^ 2 ≤ B := by
    dsimp [a, B]
    exact concrete_l2_graph_norm_candidate_add_sq_le p q
  have hsqrt_sq : (Real.sqrt B) ^ 2 = B := by
    exact Real.sq_sqrt hB
  have hsqrt_nonneg : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hle : a ≤ Real.sqrt B := by
    nlinarith
  exact hle

/-- Sqrt-form add-control package for the graph-norm candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBound : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      Real.sqrt
        ((2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
          (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2)

/-- The sqrt-form add-control package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_sqrt_add_bound :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBound := by
  exact concrete_l2_graph_norm_candidate_add_le_sqrt_bound

/--
Graph-norm candidate surface with sqrt-form add-control.

This is a direct candidate estimate.  Triangle inequality, topology, density,
and core remain downstream.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBoundSurface where
  addSquareReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurfaceReady
  sqrtAddBound : concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBound
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop

/-- Concrete sqrt-form candidate add-control surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBoundSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBoundSurface :=
  { addSquareReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound_surface_ready
    sqrtAddBound :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_sqrt_add_bound
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True }

/-- Readiness predicate for the sqrt-form candidate add-control surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBound

/-- Readiness theorem for the sqrt-form candidate add-control surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_sqrt_add_bound_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBoundSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_sqrt_add_bound⟩

end

end MathlibAnalytic
end MGAP4D
