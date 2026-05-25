import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomain

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
A raw truncation promoted to the diagonal domain is finite-support in the
concrete `l2` carrier.
-/
theorem concrete_l2_raw_truncation_promoted_finite_support
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ)
    (hsumm : Summable fun n : ℕ => (concreteL2RawTruncation x.1 N n) ^ 2)
    (hdom : ConcreteL2DiagonalDomain
      (⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence)) :
    ConcreteL2RealFiniteSupport
      (⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence) := by
  unfold ConcreteL2RealFiniteSupport
  exact concrete_l2_raw_truncation_finite_support x.1 N

/--
A raw truncation promoted to the diagonal domain defines a finite-support core
point.
-/
def concreteL2RawTruncationFiniteSupportCorePoint
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ)
    (hsumm : Summable fun n : ℕ => (concreteL2RawTruncation x.1 N n) ^ 2)
    (hdom : ConcreteL2DiagonalDomain
      (⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence)) :
    ConcreteL2DiagonalFiniteSupportDomainCarrier :=
  ⟨⟨(⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence), hdom⟩,
    concrete_l2_raw_truncation_promoted_finite_support x N hsumm hdom⟩

/--
Raw truncations promoted to the diagonal domain produce finite-support canonical
graph pairs.
-/
theorem concrete_l2_raw_truncation_mem_finite_support_core_graph
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ)
    (hsumm : Summable fun n : ℕ => (concreteL2RawTruncation x.1 N n) ^ 2)
    (hdom : ConcreteL2DiagonalDomain
      (⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence)) :
    let xN : ConcreteL2DiagonalDomainCarrier :=
      ⟨(⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence), hdom⟩
    ((xN.1, concreteL2DiagonalActionL2 xN) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier) := by
  intro xN
  refine ⟨concreteL2RawTruncationFiniteSupportCorePoint x N hsumm hdom, ?_⟩
  rfl

/-- The raw truncation finite-support graph target is ready. -/
theorem concrete_l2_raw_truncation_finite_support_graph_target_ready :
    concreteL2RawTruncationFiniteSupportGraphTarget := by
  intro x N hsumm hdom
  exact concrete_l2_raw_truncation_mem_finite_support_core_graph x N hsumm hdom

/-- Surface for the raw truncation finite-support graph theorem. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurface where
  truncationDiagonalDomainReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurfaceReady
  finiteSupportGraphTarget :
    concreteL2RawTruncationFiniteSupportGraphTarget
  boundaryNotGraphNormConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the raw truncation finite-support graph theorem. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurface :=
  { truncationDiagonalDomainReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_diagonal_domain_surface_ready
    finiteSupportGraphTarget :=
      concrete_l2_raw_truncation_finite_support_graph_target_ready
    boundaryNotGraphNormConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the raw truncation finite-support graph theorem. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDiagonalDomainSurfaceReady ∧
  concreteL2RawTruncationFiniteSupportGraphTarget

/-- Readiness theorem for the raw truncation finite-support graph theorem. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_finite_support_graph_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_diagonal_domain_surface_ready,
    concrete_l2_raw_truncation_finite_support_graph_target_ready⟩

end

end MathlibAnalytic
end MGAP4D