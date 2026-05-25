import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupport

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The support of the squared raw truncation is contained in the support of the raw
truncation.
-/
theorem concrete_l2_raw_truncation_sq_support_subset_support
    (x : ConcreteL2RealSequence) (N : ℕ) :
    ({n : ℕ | (concreteL2RawTruncation x N n) ^ 2 ≠ 0} : Set ℕ) ⊆
      ({n : ℕ | concreteL2RawTruncation x N n ≠ 0} : Set ℕ) := by
  intro n hn
  by_contra hzero
  exact hn (by rw [hzero, zero_pow two_ne_zero])

/-- The squared raw truncation has finite support. -/
theorem concrete_l2_raw_truncation_sq_has_finite_support
    (x : ConcreteL2RealSequence) (N : ℕ) :
    (fun n : ℕ => (concreteL2RawTruncation x N n) ^ 2).HasFiniteSupport := by
  exact (concrete_l2_raw_truncation_finite_support x N).subset
    (concrete_l2_raw_truncation_sq_support_subset_support x N)

/-- Raw truncations are square-summable. -/
theorem concrete_l2_raw_truncation_summable_sq
    (x : ConcreteL2RealSequence) (N : ℕ) :
    Summable fun n : ℕ => (concreteL2RawTruncation x N n) ^ 2 := by
  exact summable_of_hasFiniteSupport
    (concrete_l2_raw_truncation_sq_has_finite_support x N)

/-- The raw truncation summability target is ready. -/
theorem concrete_l2_raw_truncation_summability_target_ready :
    concreteL2RawTruncationSummabilityTarget := by
  intro x N
  exact concrete_l2_raw_truncation_summable_sq x N

/-- Surface for the raw truncation summability theorem. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurface where
  truncationFiniteSupportReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurfaceReady
  squaredSupportSubsetSupport :
    ∀ x : ConcreteL2RealSequence,
    ∀ N : ℕ,
      ({n : ℕ | (concreteL2RawTruncation x N n) ^ 2 ≠ 0} : Set ℕ) ⊆
        ({n : ℕ | concreteL2RawTruncation x N n ≠ 0} : Set ℕ)
  summabilityTarget : concreteL2RawTruncationSummabilityTarget
  finiteSupportTarget : concreteL2RawTruncationFiniteSupportTarget
  boundaryNotTruncationDiagonalDomainTheorem : Prop
  boundaryNotTruncationFiniteSupportGraphTheorem : Prop
  boundaryNotTruncationGraphNormConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the raw truncation summability theorem. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurface :=
  { truncationFiniteSupportReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_finite_support_surface_ready
    squaredSupportSubsetSupport :=
      concrete_l2_raw_truncation_sq_support_subset_support
    summabilityTarget :=
      concrete_l2_raw_truncation_summability_target_ready
    finiteSupportTarget :=
      concrete_l2_raw_truncation_finite_support_target_ready
    boundaryNotTruncationDiagonalDomainTheorem := True
    boundaryNotTruncationFiniteSupportGraphTheorem := True
    boundaryNotTruncationGraphNormConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the raw truncation summability theorem. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportSurfaceReady ∧
  concreteL2RawTruncationFiniteSupportTarget ∧
  concreteL2RawTruncationSummabilityTarget

/-- Readiness theorem for the raw truncation summability theorem. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_summability_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationSummabilitySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_finite_support_surface_ready,
    concrete_l2_raw_truncation_finite_support_target_ready,
    concrete_l2_raw_truncation_summability_target_ready⟩

end

end MathlibAnalytic
end MGAP4D