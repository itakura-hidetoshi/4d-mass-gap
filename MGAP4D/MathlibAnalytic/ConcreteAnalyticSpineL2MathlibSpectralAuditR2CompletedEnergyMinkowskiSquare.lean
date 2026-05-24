import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Exact completed-energy expansion for addition of graph pairs.

This is the infinite-sum version of the pointwise identity
`energy(p+q,n) = energy(p,n)+energy(q,n)+2*cross(p,q,n)`.
-/
theorem concrete_l2_completed_graph_energy_add_exact_expansion
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) =
      concreteL2CompletedGraphEnergy p + concreteL2CompletedGraphEnergy q +
        (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) := by
  unfold concreteL2CompletedGraphEnergy
  have hp : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm p n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable p
  have hq : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm q n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable q
  have hcross : Summable fun n : ℕ => concreteL2GraphPairCrossTerm p q n :=
    concrete_l2_graph_pair_cross_term_summable p q
  have hpq : Summable fun n : ℕ =>
      concreteL2GraphPairEnergyTerm p n + concreteL2GraphPairEnergyTerm q n :=
    hp.add hq
  have h2cross : Summable fun n : ℕ =>
      (2 : ℝ) * concreteL2GraphPairCrossTerm p q n := by
    simpa using hcross.mul_left (2 : ℝ)
  have hsum : Summable fun n : ℕ =>
      concreteL2GraphPairEnergyTerm p n + concreteL2GraphPairEnergyTerm q n +
        (2 : ℝ) * concreteL2GraphPairCrossTerm p q n :=
    hpq.add h2cross
  have hfun :
      (fun n : ℕ => concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n) =
        (fun n : ℕ =>
          concreteL2GraphPairEnergyTerm p n + concreteL2GraphPairEnergyTerm q n +
            (2 : ℝ) * concreteL2GraphPairCrossTerm p q n) := by
    funext n
    exact concrete_l2_graph_pair_energy_add_exact_expansion p q n
  rw [hfun]
  calc
    (∑' n : ℕ,
        (concreteL2GraphPairEnergyTerm p n + concreteL2GraphPairEnergyTerm q n +
          (2 : ℝ) * concreteL2GraphPairCrossTerm p q n))
        = (∑' n : ℕ,
            (concreteL2GraphPairEnergyTerm p n + concreteL2GraphPairEnergyTerm q n)) +
            (∑' n : ℕ, (2 : ℝ) * concreteL2GraphPairCrossTerm p q n) := by
          exact hpq.tsum_add h2cross
    _ = ((∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) +
            (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n)) +
            (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) := by
          rw [hp.tsum_add hq]
          rw [(tsum_mul_left :
            (∑' n : ℕ, (2 : ℝ) * concreteL2GraphPairCrossTerm p q n) =
              (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n))]
    _ = (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) +
          (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n) +
            (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) := by
          ring

/--
Completed-energy Minkowski square bound.

This is the sharp completed-energy estimate behind the exact triangle
inequality for the graph-norm candidate.
-/
theorem concrete_l2_completed_energy_minkowski_square
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) ≤
      (Real.sqrt (concreteL2CompletedGraphEnergy p) +
        Real.sqrt (concreteL2CompletedGraphEnergy q)) ^ 2 := by
  let Ep := concreteL2CompletedGraphEnergy p
  let Eq := concreteL2CompletedGraphEnergy q
  let C := ∑' n : ℕ, concreteL2GraphPairCrossTerm p q n
  have hEp : 0 ≤ Ep := by
    dsimp [Ep]
    exact concrete_l2_completed_graph_energy_nonneg p
  have hEq : 0 ≤ Eq := by
    dsimp [Eq]
    exact concrete_l2_completed_graph_energy_nonneg q
  have hcross : C ≤ Real.sqrt Ep * Real.sqrt Eq := by
    dsimp [C, Ep, Eq]
    exact concrete_l2_cross_term_summed_cauchy p q
  have hexp :
      concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) =
        Ep + Eq + (2 : ℝ) * C := by
    dsimp [Ep, Eq, C]
    exact concrete_l2_completed_graph_energy_add_exact_expansion p q
  have hsquare :
      (Real.sqrt Ep + Real.sqrt Eq) ^ 2 =
        Ep + Eq + (2 : ℝ) * (Real.sqrt Ep * Real.sqrt Eq) := by
    have hsqEp : (Real.sqrt Ep) ^ 2 = Ep := Real.sq_sqrt hEp
    have hsqEq : (Real.sqrt Eq) ^ 2 = Eq := Real.sq_sqrt hEq
    rw [add_sq, hsqEp, hsqEq]
    ring
  rw [hexp, hsquare]
  nlinarith

/-- Package: completed-energy Minkowski square bound. -/
def concreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquare : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) ≤
      (Real.sqrt (concreteL2CompletedGraphEnergy p) +
        Real.sqrt (concreteL2CompletedGraphEnergy q)) ^ 2

/-- The completed-energy Minkowski square package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_completed_energy_minkowski_square :
    concreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquare := by
  intro p q
  exact concrete_l2_completed_energy_minkowski_square p q

/-- Surface for completed-energy Minkowski square bound. -/
structure ConcreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurface where
  crossTermSummedReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchySurfaceReady
  energyExpansion : ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) =
      concreteL2CompletedGraphEnergy p + concreteL2CompletedGraphEnergy q +
        (2 : ℝ) * (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n)
  minkowskiSquare : concreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquare
  boundaryNotExactTriangle : Prop
  boundaryNotTopology : Prop

/-- Concrete surface for completed-energy Minkowski square bound. -/
def concreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurface :
    ConcreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurface :=
  { crossTermSummedReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_surface_ready
    energyExpansion := concrete_l2_completed_graph_energy_add_exact_expansion
    minkowskiSquare :=
      concrete_l2_mathlib_spectral_audit_r2_completed_energy_minkowski_square
    boundaryNotExactTriangle := True
    boundaryNotTopology := True }

/-- Readiness predicate for completed-energy Minkowski square. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquare

/-- Readiness theorem for completed-energy Minkowski square. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_energy_minkowski_square_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedEnergyMinkowskiSquareSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_completed_energy_minkowski_square⟩

end

end MathlibAnalytic
end MGAP4D
