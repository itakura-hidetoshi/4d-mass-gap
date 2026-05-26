import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TailItePrefixZero

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Every finite prefix of the target tail-`ite` series is bounded by the
corresponding finite prefix of the full target graph-energy series.

This is the finite monotonicity step coming directly from the pointwise
domination `tailIte n ≤ targetEnergy n`.
-/
theorem concrete_l2_target_tail_ite_range_sum_le_target_range_sum
    (x : ConcreteL2DiagonalDomainCarrier) (N M : ℕ) :
    Finset.sum (Finset.range M)
      (fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n) ≤
      Finset.sum (Finset.range M)
        (fun n : ℕ =>
          concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) := by
  exact Finset.sum_le_sum fun n _hn =>
    concrete_l2_target_graph_energy_tail_ite_le_target x N n

/--
Every finite prefix of the target tail-`ite` series is bounded by the completed
energy of the full target diagonal graph.

The proof is the clean two-step Mathlib route:

1. compare finite sums pointwise;
2. bound the target finite prefix by the completed `tsum` using the existing
   `sum_le_tsum` prefix-order theorem.
-/
theorem concrete_l2_target_tail_ite_range_sum_le_completed_target
    (x : ConcreteL2DiagonalDomainCarrier) (N M : ℕ) :
    Finset.sum (Finset.range M)
      (fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n) ≤
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) := by
  exact le_trans
    (concrete_l2_target_tail_ite_range_sum_le_target_range_sum x N M)
    (concrete_l2_graph_energy_range_prefix_le_completed
      (x.1, concreteL2DiagonalActionL2 x) M)

/--
The completed truncation-error graph energy is nonnegative.
-/
theorem concrete_l2_completed_truncation_error_energy_nonneg
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    0 ≤ concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N) := by
  exact concrete_l2_completed_graph_energy_nonneg
    (concreteL2RawTruncationGraphError x N)

/--
The completed target tail-`ite` `tsum` is nonnegative.
-/
theorem concrete_l2_target_tail_ite_tsum_nonneg
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    0 ≤ ∑' n : ℕ, concreteL2TargetGraphEnergyTailIte x N n := by
  exact tsum_nonneg fun n =>
    concrete_l2_target_graph_energy_tail_ite_nonneg x N n

/--
Finite-budget package for the target tail-`ite` route.
-/
def concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetPackage : Prop :=
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N M : ℕ,
      Finset.sum (Finset.range M)
        (fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n) ≤
        Finset.sum (Finset.range M)
          (fun n : ℕ =>
            concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n)) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N M : ℕ,
      Finset.sum (Finset.range M)
        (fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n) ≤
        concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x)) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      0 ≤ concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N)) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      0 ≤ ∑' n : ℕ, concreteL2TargetGraphEnergyTailIte x N n)

/-- The finite-budget package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_tail_ite_finite_budget_package_ready :
    concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetPackage := by
  exact ⟨
    concrete_l2_target_tail_ite_range_sum_le_target_range_sum,
    concrete_l2_target_tail_ite_range_sum_le_completed_target,
    concrete_l2_completed_truncation_error_energy_nonneg,
    concrete_l2_target_tail_ite_tsum_nonneg⟩

/--
Boundary retained after finite-budget control.

This file proves finite-prefix domination and nonnegativity.  The exact completed
`tsum` subtraction/comparison theorem remains the next step.
-/
def concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetBoundaryHeld : Prop :=
  True

/-- Surface for finite-budget control of the tail-`ite` route. -/
structure ConcreteL2MathlibSpectralAuditR2TailIteFiniteBudgetSurface where
  prefixZeroReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailItePrefixZeroSurfaceReady
  finiteBudgetPackage : concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetPackage
  boundaryHeld : concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetBoundaryHeld
  boundaryNotTailTsumSubPrefix : Prop
  boundaryNotCompletedEnergyComparison : Prop
  boundaryNotTailSmallnessClosed : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for finite-budget control. -/
def concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetSurface :
    ConcreteL2MathlibSpectralAuditR2TailIteFiniteBudgetSurface :=
  { prefixZeroReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_prefix_zero_surface_ready
    finiteBudgetPackage :=
      concrete_l2_mathlib_spectral_audit_r2_tail_ite_finite_budget_package_ready
    boundaryHeld := True.intro
    boundaryNotTailTsumSubPrefix := True
    boundaryNotCompletedEnergyComparison := True
    boundaryNotTailSmallnessClosed := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for finite-budget control. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteFiniteBudgetSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TailItePrefixZeroSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetPackage ∧
  concreteL2MathlibSpectralAuditR2TailIteFiniteBudgetBoundaryHeld

/-- Readiness theorem for finite-budget control. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_finite_budget_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailIteFiniteBudgetSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_ite_prefix_zero_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_tail_ite_finite_budget_package_ready,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
