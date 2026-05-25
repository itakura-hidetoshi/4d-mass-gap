import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquare

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The graph-norm candidate is the square root of completed graph energy.

The project already has the squared identity and nonnegativity; this lemma is a
small bridge used to rewrite the sharp completed-energy Minkowski square bound
as the exact triangle inequality for the candidate.
-/
theorem concrete_l2_graph_norm_candidate_eq_sqrt_completed_energy
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate p = Real.sqrt (concreteL2CompletedGraphEnergy p) := by
  have hcandidate_nonneg : 0 ≤ concreteL2GraphNormCandidate p :=
    concrete_l2_graph_norm_candidate_nonneg p
  have henergy_nonneg : 0 ≤ concreteL2CompletedGraphEnergy p :=
    concrete_l2_completed_graph_energy_nonneg p
  have hsq : concreteL2GraphNormCandidate p ^ 2 = concreteL2CompletedGraphEnergy p :=
    concrete_l2_graph_norm_candidate_sq p
  have hsqrt_sq :
      (Real.sqrt (concreteL2CompletedGraphEnergy p)) ^ 2 =
        concreteL2CompletedGraphEnergy p :=
    Real.sq_sqrt henergy_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt (concreteL2CompletedGraphEnergy p) :=
    Real.sqrt_nonneg _
  nlinarith

/--
Exact triangle inequality for the concrete graph-norm candidate.
-/
theorem concrete_l2_graph_norm_candidate_triangle
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      concreteL2GraphNormCandidate p + concreteL2GraphNormCandidate q := by
  let a := concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q)
  let b := concreteL2GraphNormCandidate p + concreteL2GraphNormCandidate q
  have ha : 0 ≤ a := by
    dsimp [a]
    exact concrete_l2_graph_norm_candidate_nonneg (concreteL2GraphPairAdd p q)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg
      (concrete_l2_graph_norm_candidate_nonneg p)
      (concrete_l2_graph_norm_candidate_nonneg q)
  have hM := concrete_l2_completed_energy_minkowski_square p q
  have hsq_a : a ^ 2 = concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) := by
    dsimp [a]
    exact concrete_l2_graph_norm_candidate_sq (concreteL2GraphPairAdd p q)
  have hp_sqrt :
      concreteL2GraphNormCandidate p = Real.sqrt (concreteL2CompletedGraphEnergy p) :=
    concrete_l2_graph_norm_candidate_eq_sqrt_completed_energy p
  have hq_sqrt :
      concreteL2GraphNormCandidate q = Real.sqrt (concreteL2CompletedGraphEnergy q) :=
    concrete_l2_graph_norm_candidate_eq_sqrt_completed_energy q
  have hright :
      (Real.sqrt (concreteL2CompletedGraphEnergy p) +
          Real.sqrt (concreteL2CompletedGraphEnergy q)) ^ 2 = b ^ 2 := by
    dsimp [b]
    rw [hp_sqrt, hq_sqrt]
  have hsq_le : a ^ 2 ≤ b ^ 2 := by
    calc
      a ^ 2 = concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) := hsq_a
      _ ≤ (Real.sqrt (concreteL2CompletedGraphEnergy p) +
            Real.sqrt (concreteL2CompletedGraphEnergy q)) ^ 2 := hM
      _ = b ^ 2 := hright
  nlinarith

/-- Package: exact triangle inequality for the graph-norm candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateTriangle : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      concreteL2GraphNormCandidate p + concreteL2GraphNormCandidate q

/-- The exact graph-norm candidate triangle package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_triangle :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateTriangle := by
  intro p q
  exact concrete_l2_graph_norm_candidate_triangle p q

/-- Surface for the exact triangle inequality. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormExactTriangleSurface where
  minkowskiSquareReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurfaceReady
  candidateSqrtEnergy : ∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate p = Real.sqrt (concreteL2CompletedGraphEnergy p)
  triangle : concreteL2MathlibSpectralAuditR2GraphNormCandidateTriangle
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete exact triangle surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormExactTriangleSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormExactTriangleSurface :=
  { minkowskiSquareReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_energy_minkowski_square_surface_ready
    candidateSqrtEnergy := concrete_l2_graph_norm_candidate_eq_sqrt_completed_energy
    triangle := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_triangle
    boundaryNotTopology := True
    boundaryNotDensity := True
    boundaryNotCore := True }

/-- Readiness predicate for the exact triangle surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormExactTriangleSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateTriangle

/-- Readiness theorem for the exact triangle surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_exact_triangle_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormExactTriangleSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_energy_minkowski_square_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_triangle⟩

end

end MathlibAnalytic
end MGAP4D
