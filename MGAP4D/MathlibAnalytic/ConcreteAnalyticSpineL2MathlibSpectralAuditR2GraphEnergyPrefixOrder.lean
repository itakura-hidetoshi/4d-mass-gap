import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZero

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Every finite graph-energy prefix is bounded by the completed graph energy.
-/
theorem concrete_l2_graph_energy_prefix_le_completed
    (p : ConcreteL2GraphPairSpace) (u : Finset ℕ) :
    Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ≤
      concreteL2CompletedGraphEnergy p := by
  unfold concreteL2CompletedGraphEnergy
  exact (concrete_l2_completed_graph_energy_summable p).sum_le_tsum u
    (fun n hn => concrete_l2_graph_pair_energy_term_nonneg p n)

/-- Range-prefix specialization of the completed graph-energy order bound. -/
theorem concrete_l2_graph_energy_range_prefix_le_completed
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    Finset.sum (Finset.range N)
      (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ≤
      concreteL2CompletedGraphEnergy p := by
  exact concrete_l2_graph_energy_prefix_le_completed p (Finset.range N)

/-- Range-prefix deficit is nonnegative. -/
theorem concrete_l2_graph_energy_range_prefix_deficit_nonneg
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    0 ≤ concreteL2CompletedGraphEnergy p -
      Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) := by
  exact sub_nonneg.mpr (concrete_l2_graph_energy_range_prefix_le_completed p N)

/-- Surface for graph-energy finite-prefix order bounds. -/
structure ConcreteL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurface where
  prefixZeroReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurfaceReady
  prefixLeCompleted :
    ∀ p : ConcreteL2GraphPairSpace,
    ∀ u : Finset ℕ,
      Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ≤
        concreteL2CompletedGraphEnergy p
  completedEnergyNonneg :
    ∀ p : ConcreteL2GraphPairSpace,
      0 ≤ concreteL2CompletedGraphEnergy p
  rangePrefixDeficitNonneg :
    ∀ p : ConcreteL2GraphPairSpace,
    ∀ N : ℕ,
      0 ≤ concreteL2CompletedGraphEnergy p -
        Finset.sum (Finset.range N)
          (fun n : ℕ => concreteL2GraphPairEnergyTerm p n)
  boundaryNotTailEnergyTheorem : Prop
  boundaryNotTruncationEnergyEpsilonTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for graph-energy finite-prefix order bounds. -/
def concreteL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurface :
    ConcreteL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurface :=
  { prefixZeroReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_prefix_zero_surface_ready
    prefixLeCompleted :=
      concrete_l2_graph_energy_prefix_le_completed
    completedEnergyNonneg :=
      concrete_l2_completed_graph_energy_nonneg
    rangePrefixDeficitNonneg :=
      concrete_l2_graph_energy_range_prefix_deficit_nonneg
    boundaryNotTailEnergyTheorem := True
    boundaryNotTruncationEnergyEpsilonTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for graph-energy finite-prefix order bounds. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurfaceReady ∧
  (∀ p : ConcreteL2GraphPairSpace,
    ∀ u : Finset ℕ,
      Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ≤
        concreteL2CompletedGraphEnergy p) ∧
  (∀ p : ConcreteL2GraphPairSpace,
      0 ≤ concreteL2CompletedGraphEnergy p)

/-- Readiness theorem for graph-energy finite-prefix order bounds. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_energy_prefix_order_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_prefix_zero_surface_ready,
    concrete_l2_graph_energy_prefix_le_completed,
    concrete_l2_completed_graph_energy_nonneg⟩

end

end MathlibAnalytic
end MGAP4D