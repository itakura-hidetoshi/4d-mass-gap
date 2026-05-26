import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TailIteFiniteBudget

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The completed `tsum` of the target tail-`ite` series is bounded by the completed
energy of the full target diagonal graph.

This is the direct completed-series analogue of the finite-budget lemma.  It is
proved by Mathlib's summable `tsum` comparison from:

* pointwise domination of the tail-`ite` terms by the target graph-energy terms;
* summability of the tail-`ite` series;
* summability of the full target graph-energy series.
-/
theorem concrete_l2_target_tail_ite_tsum_le_completed_target
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    (∑' n : ℕ, concreteL2TargetGraphEnergyTailIte x N n) ≤
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) := by
  unfold concreteL2CompletedGraphEnergy
  exact Summable.tsum_le_tsum
    (fun n : ℕ => concrete_l2_target_graph_energy_tail_ite_le_target x N n)
    (concrete_l2_target_graph_energy_tail_ite_summable x N)
    (concrete_l2_completed_graph_energy_summable (x.1, concreteL2DiagonalActionL2 x))

/--
The completed raw truncation graph-error energy is bounded by the completed
energy of the full target diagonal graph.
-/
theorem concrete_l2_completed_truncation_error_energy_le_completed_target
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N) ≤
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) := by
  rw [concrete_l2_completed_truncation_error_energy_eq_tail_ite_tsum x N]
  exact concrete_l2_target_tail_ite_tsum_le_completed_target x N

/--
Completed-budget package for the target tail-`ite` route.
-/
def concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedPackage : Prop :=
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      (∑' n : ℕ, concreteL2TargetGraphEnergyTailIte x N n) ≤
        concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x)) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N) ≤
        concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x))

/-- The completed-budget package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_tail_ite_tsum_le_completed_package_ready :
    concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedPackage := by
  exact ⟨
    concrete_l2_target_tail_ite_tsum_le_completed_target,
    concrete_l2_completed_truncation_error_energy_le_completed_target⟩

/--
Boundary retained after completed-budget control.

This file proves the completed `tsum` budget bound.  The sharper subtraction
comparison `tail ≤ completed - prefix` remains downstream.
-/
def concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedBoundaryHeld : Prop :=
  True

/-- Surface for completed-budget control of the tail-`ite` route. -/
structure ConcreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedSurface where
  finiteBudgetReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteFiniteBudgetSurfaceReady
  completedBudgetPackage : concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedPackage
  boundaryHeld : concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedBoundaryHeld
  boundaryNotTailTsumSubPrefix : Prop
  boundaryNotCompletedEnergyPrefixDeficitComparison : Prop
  boundaryNotTailSmallnessClosed : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for completed-budget control. -/
def concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedSurface :
    ConcreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedSurface :=
  { finiteBudgetReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_finite_budget_surface_ready
    completedBudgetPackage :=
      concrete_l2_mathlib_spectral_audit_r2_tail_ite_tsum_le_completed_package_ready
    boundaryHeld := True.intro
    boundaryNotTailTsumSubPrefix := True
    boundaryNotCompletedEnergyPrefixDeficitComparison := True
    boundaryNotTailSmallnessClosed := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for completed-budget control. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteTsumLeCompletedSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteFiniteBudgetSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedPackage ∧
  concreteL2MathlibSpectralAuditR2TailIteTsumLeCompletedBoundaryHeld

/-- Readiness theorem for completed-budget control. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_tsum_le_completed_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteTsumLeCompletedSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_finite_budget_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_tail_ite_tsum_le_completed_package_ready,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
