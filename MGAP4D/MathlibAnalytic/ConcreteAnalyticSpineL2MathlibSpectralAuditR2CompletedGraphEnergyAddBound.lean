import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneity

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Completed graph-energy add-control.

This lifts the pointwise graph-pair add-energy estimate through `tsum` and
rewrites the right side as completed energies.  It is the main analytic bridge
immediately below the graph-norm triangle inequality.
-/
theorem concrete_l2_completed_graph_energy_add_le
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) ≤
      (2 : ℝ) * concreteL2CompletedGraphEnergy p +
        (2 : ℝ) * concreteL2CompletedGraphEnergy q := by
  unfold concreteL2CompletedGraphEnergy
  have hleft : Summable fun n : ℕ =>
      concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable (concreteL2GraphPairAdd p q)
  have hp : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm p n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable p
  have hq : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm q n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable q
  have hp2 : Summable fun n : ℕ => (2 : ℝ) * concreteL2GraphPairEnergyTerm p n := by
    simpa using hp.mul_left (2 : ℝ)
  have hq2 : Summable fun n : ℕ => (2 : ℝ) * concreteL2GraphPairEnergyTerm q n := by
    simpa using hq.mul_left (2 : ℝ)
  have hright : Summable fun n : ℕ =>
      (2 : ℝ) * concreteL2GraphPairEnergyTerm p n +
        (2 : ℝ) * concreteL2GraphPairEnergyTerm q n :=
    hp2.add hq2
  have hpoint : ∀ n : ℕ,
      concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n ≤
        (2 : ℝ) * concreteL2GraphPairEnergyTerm p n +
          (2 : ℝ) * concreteL2GraphPairEnergyTerm q n := by
    intro n
    simpa [smul_eq_mul] using
      concrete_l2_mathlib_spectral_audit_r2_graph_energy_add_control p q n
  have hle :
      (∑' n : ℕ, concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n) ≤
        ∑' n : ℕ,
          ((2 : ℝ) * concreteL2GraphPairEnergyTerm p n +
            (2 : ℝ) * concreteL2GraphPairEnergyTerm q n) := by
    exact hleft.tsum_le_tsum hpoint hright
  have hsplit :
      (∑' n : ℕ,
          ((2 : ℝ) * concreteL2GraphPairEnergyTerm p n +
            (2 : ℝ) * concreteL2GraphPairEnergyTerm q n)) =
        (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) +
          (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n) := by
    calc
      (∑' n : ℕ,
          ((2 : ℝ) * concreteL2GraphPairEnergyTerm p n +
            (2 : ℝ) * concreteL2GraphPairEnergyTerm q n))
          = (∑' n : ℕ, (2 : ℝ) * concreteL2GraphPairEnergyTerm p n) +
              (∑' n : ℕ, (2 : ℝ) * concreteL2GraphPairEnergyTerm q n) := by
              exact hp2.tsum_add hq2
      _ = (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) +
            (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n) := by
              rw [
                (tsum_mul_left :
                  (∑' n : ℕ, (2 : ℝ) * concreteL2GraphPairEnergyTerm p n) =
                    (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n)),
                (tsum_mul_left :
                  (∑' n : ℕ, (2 : ℝ) * concreteL2GraphPairEnergyTerm q n) =
                    (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n))]
  exact le_trans hle (le_of_eq hsplit)

/-- Completed graph-energy add-control package. -/
def concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) ≤
      (2 : ℝ) * concreteL2CompletedGraphEnergy p +
        (2 : ℝ) * concreteL2CompletedGraphEnergy q

/-- The completed graph-energy add-control package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound :
    concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound := by
  exact concrete_l2_completed_graph_energy_add_le

/--
Completed graph-energy add-control surface.

This is a pre-triangle surface.  It does not yet prove the graph-norm candidate
triangle inequality, but it is the completed-energy estimate from which such a
theorem should be derived.
-/
structure ConcreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurface where
  homogeneityReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurfaceReady
  addBound : concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop

/-- Concrete completed graph-energy add-control surface. -/
def concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurface :
    ConcreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurface :=
  { homogeneityReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_homogeneity_surface_ready
    addBound := concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True }

/-- Readiness predicate for the completed graph-energy add-control surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound

/-- Readiness theorem for the completed graph-energy add-control surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_homogeneity_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound⟩

end

end MathlibAnalytic
end MGAP4D
