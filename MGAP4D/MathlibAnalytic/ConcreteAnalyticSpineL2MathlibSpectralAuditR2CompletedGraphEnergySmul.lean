import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquare

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Completed graph energy under scalar multiplication.

This lifts the pointwise scalar square-energy law through `tsum`.  It is a real
energy identity, still below the level of a full graph-norm homogeneity theorem.
-/
theorem concrete_l2_completed_graph_energy_smul
    (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2CompletedGraphEnergy (concreteL2GraphPairSmul c p) =
      (c ^ 2) * concreteL2CompletedGraphEnergy p := by
  unfold concreteL2CompletedGraphEnergy
  calc
    (∑' n : ℕ, concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) n)
        = ∑' n : ℕ, (c ^ 2) • concreteL2GraphPairEnergyTerm p n := by
          congr 1
          funext n
          exact concrete_l2_mathlib_spectral_audit_r2_graph_energy_smul_law c p n
    _ = (c ^ 2) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) := by
          rw [tsum_const_smul]
          rfl

/-- Completed graph-energy scalar law package. -/
def concreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulLaw : Prop :=
  ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2CompletedGraphEnergy (concreteL2GraphPairSmul c p) =
      (c ^ 2) * concreteL2CompletedGraphEnergy p

/-- The completed graph-energy scalar law is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_smul_law :
    concreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulLaw := by
  exact concrete_l2_completed_graph_energy_smul

/--
Completed graph-energy scalar surface.
-/
structure ConcreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurface where
  squareReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady
  smulLaw : concreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulLaw
  boundaryNotNormHomogeneity : Prop
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop

/-- Concrete completed graph-energy scalar surface. -/
def concreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurface :
    ConcreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurface :=
  { squareReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_surface_ready
    smulLaw := concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_smul_law
    boundaryNotNormHomogeneity := True
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True }

/-- Readiness predicate for the completed graph-energy scalar surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CompletedGraphEnergySmulLaw

/-- Readiness theorem for the completed graph-energy scalar surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_smul_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_smul_law⟩

end

end MathlibAnalytic
end MGAP4D
