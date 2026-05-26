import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The finite range prefixes of the graph-pair energy series converge to the
completed graph energy.

This is the standard `Summable.hasSum.tendsto_sum_nat` bridge specialized to the
completed graph-energy functional.
-/
theorem concrete_l2_completed_graph_energy_prefix_tendsto
    (p : ConcreteL2GraphPairSpace) :
    Filter.Tendsto
      (fun N : ℕ => Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm p n))
      Filter.atTop
      (nhds (concreteL2CompletedGraphEnergy p)) := by
  unfold concreteL2CompletedGraphEnergy
  exact (concrete_l2_completed_graph_energy_summable p).hasSum.tendsto_sum_nat

/--
Metric ε-form of graph-energy prefix convergence.
-/
theorem concrete_l2_completed_graph_energy_prefix_eventually_close
    (p : ConcreteL2GraphPairSpace) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop,
      |Finset.sum (Finset.range N)
          (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) -
        concreteL2CompletedGraphEnergy p| < ε := by
  have hconv := concrete_l2_completed_graph_energy_prefix_tendsto p
  rw [Metric.tendsto_nhds] at hconv
  specialize hconv ε hε
  filter_upwards [hconv] with N hN
  simpa [Real.dist_eq, abs_sub_comm] using hN

/-- Surface for completed graph-energy prefix convergence. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurface where
  energyEpsilonBridgeReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurfaceReady
  prefixTendsto :
    ∀ p : ConcreteL2GraphPairSpace,
      Filter.Tendsto
        (fun N : ℕ => Finset.sum (Finset.range N)
          (fun n : ℕ => concreteL2GraphPairEnergyTerm p n))
        Filter.atTop
        (nhds (concreteL2CompletedGraphEnergy p))
  prefixEventuallyClose :
    ∀ p : ConcreteL2GraphPairSpace,
    ∀ ε : ℝ,
      0 < ε →
        ∀ᶠ N in Filter.atTop,
          |Finset.sum (Finset.range N)
              (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) -
            concreteL2CompletedGraphEnergy p| < ε
  boundaryNotTailEnergyTheorem : Prop
  boundaryNotTruncationEnergyEpsilonTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for completed graph-energy prefix convergence. -/
def concreteL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurface :=
  { energyEpsilonBridgeReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_energy_epsilon_bridge_surface_ready
    prefixTendsto :=
      concrete_l2_completed_graph_energy_prefix_tendsto
    prefixEventuallyClose :=
      concrete_l2_completed_graph_energy_prefix_eventually_close
    boundaryNotTailEnergyTheorem := True
    boundaryNotTruncationEnergyEpsilonTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for completed graph-energy prefix convergence. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurfaceReady ∧
  (∀ p : ConcreteL2GraphPairSpace,
    Filter.Tendsto
      (fun N : ℕ => Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm p n))
      Filter.atTop
      (nhds (concreteL2CompletedGraphEnergy p)))

/-- Readiness theorem for completed graph-energy prefix convergence. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_energy_prefix_limit_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_energy_epsilon_bridge_surface_ready,
    concrete_l2_completed_graph_energy_prefix_tendsto⟩

end

end MathlibAnalytic
end MGAP4D