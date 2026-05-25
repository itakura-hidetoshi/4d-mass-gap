import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationSummability

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Weighted truncation support is contained in truncation support. -/
theorem concrete_l2_raw_truncation_weighted_support_subset
    (x : ConcreteL2RealSequence) (N n : ℕ)
    (hzero : concreteL2RawTruncation x N n = 0) :
    (concreteL2DiagonalWeight n) ^ 2 *
        (concreteL2RawTruncation x N n) ^ 2 = 0 := by
  rw [hzero]
  ring

/-- Weighted truncation square sequence has finite support. -/
theorem concrete_l2_raw_truncation_weighted_has_finite_support
    (x : ConcreteL2RealSequence) (N : ℕ) :
    (fun n : ℕ =>
      (concreteL2DiagonalWeight n) ^ 2 *
        (concreteL2RawTruncation x N n) ^ 2).HasFiniteSupport := by
  refine (concrete_l2_raw_truncation_finite_support x N).subset ?_
  intro n hn hzero
  exact hn (by
    exact_mod_cast
      concrete_l2_raw_truncation_weighted_support_subset x N n hzero)

/-- Weighted truncation square sequence is summable. -/
theorem concrete_l2_raw_truncation_weighted_summable
    (x : ConcreteL2RealSequence) (N : ℕ) :
    Summable (fun n : ℕ =>
      (concreteL2DiagonalWeight n) ^ 2 *
        (concreteL2RawTruncation x N n) ^ 2) := by
  exact summable_of_hasFiniteSupport
    (concrete_l2_raw_truncation_weighted_has_finite_support x N)

/-- Raw truncations lie in the diagonal domain. -/
theorem concrete_l2_raw_truncation_mem_diagonal_domain
    (x : ConcreteL2RealSequence) (N : ℕ) :
    ConcreteL2DiagonalDomain
      ⟨concreteL2RawTruncation x N,
        concrete_l2_raw_truncation_summable_sq x N⟩ := by
  unfold ConcreteL2DiagonalDomain
  exact concrete_l2_raw_truncation_weighted_summable x N

/-- The raw truncation diagonal-domain target is ready. -/
theorem concrete_l2_raw_truncation_diagonal_domain_target_ready :
    concreteL2RawTruncationDiagonalDomainTarget := by
  intro x N
  exact concrete_l2_raw_truncation_mem_diagonal_domain x.1 N

/-- Surface for the raw truncation diagonal-domain theorem. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurface where
  truncationSummabilityReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurfaceReady
  diagonalDomainTarget :
    concreteL2RawTruncationDiagonalDomainTarget
  boundaryNotFiniteSupportGraphTheorem : Prop
  boundaryNotGraphNormConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the raw truncation diagonal-domain theorem. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurface :=
  { truncationSummabilityReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_summability_surface_ready
    diagonalDomainTarget :=
      concrete_l2_raw_truncation_diagonal_domain_target_ready
    boundaryNotFiniteSupportGraphTheorem := True
    boundaryNotGraphNormConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the raw truncation diagonal-domain theorem. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurfaceReady ∧
  concreteL2RawTruncationDiagonalDomainTarget

/-- Readiness theorem for the raw truncation diagonal-domain theorem. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_diagonal_domain_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_summability_surface_ready,
    concrete_l2_raw_truncation_diagonal_domain_target_ready⟩

end

end MathlibAnalytic
end MGAP4D