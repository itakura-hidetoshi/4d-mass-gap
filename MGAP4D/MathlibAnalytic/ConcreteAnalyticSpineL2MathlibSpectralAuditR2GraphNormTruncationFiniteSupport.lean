import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationTargets

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The support of the raw truncation is contained in the finite initial interval
`Finset.range N`.
-/
theorem concrete_l2_raw_truncation_support_subset_range
    (x : ConcreteL2RealSequence) (N : ℕ) :
    ({n : ℕ | concreteL2RawTruncation x N n ≠ 0} : Set ℕ) ⊆
      (Finset.range N : Set ℕ) := by
  intro n hn
  by_contra hnot
  have hzero : concreteL2RawTruncation x N n = 0 := by
    exact concrete_l2_raw_truncation_eq_zero_of_not_lt x N n hnot
  exact hn hzero

/-- Raw truncations have finite support. -/
theorem concrete_l2_raw_truncation_finite_support
    (x : ConcreteL2RealSequence) (N : ℕ) :
    ({n : ℕ | concreteL2RawTruncation x N n ≠ 0} : Set ℕ).Finite := by
  exact (Finset.finite_toSet (Finset.range N)).subset
    (concrete_l2_raw_truncation_support_subset_range x N)

/-- The raw truncation finite-support target is ready. -/
theorem concrete_l2_raw_truncation_finite_support_target_ready :
    concreteL2RawTruncationFiniteSupportTarget := by
  intro x N
  exact concrete_l2_raw_truncation_finite_support x N

/-- Surface for the raw truncation finite-support theorem. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurface where
  truncationTargetsReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurfaceReady
  supportSubsetRange :
    ∀ x : ConcreteL2RealSequence,
    ∀ N : ℕ,
      ({n : ℕ | concreteL2RawTruncation x N n ≠ 0} : Set ℕ) ⊆
        (Finset.range N : Set ℕ)
  finiteSupportTarget : concreteL2RawTruncationFiniteSupportTarget
  boundaryNotTruncationSummabilityTheorem : Prop
  boundaryNotTruncationDiagonalDomainTheorem : Prop
  boundaryNotTruncationGraphNormConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the raw truncation finite-support theorem. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurface :=
  { truncationTargetsReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_targets_surface_ready
    supportSubsetRange :=
      concrete_l2_raw_truncation_support_subset_range
    finiteSupportTarget :=
      concrete_l2_raw_truncation_finite_support_target_ready
    boundaryNotTruncationSummabilityTheorem := True
    boundaryNotTruncationDiagonalDomainTheorem := True
    boundaryNotTruncationGraphNormConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the raw truncation finite-support theorem. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurfaceReady ∧
  concreteL2RawTruncationFiniteSupportTarget

/-- Readiness theorem for the raw truncation finite-support theorem. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_finite_support_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_targets_surface_ready,
    concrete_l2_raw_truncation_finite_support_target_ready⟩

end

end MathlibAnalytic
end MGAP4D