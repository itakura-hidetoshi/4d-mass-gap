import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDomainSequenceBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Raw coordinate truncation of a concrete `l2` sequence.

The cutoff convention is `n < N`.  This is only the raw scalar sequence; the next
layers must separately prove `l2` summability, finite support, diagonal-domain
membership, and graph-norm convergence.
-/
def concreteL2RawTruncation
    (x : ConcreteL2RealSequence) (N : ℕ) : ℕ → ℝ :=
  fun n => if n < N then x.1 n else 0

/-- Inside the cutoff, raw truncation agrees with the original sequence. -/
theorem concrete_l2_raw_truncation_eq_of_lt
    (x : ConcreteL2RealSequence) (N n : ℕ) (hn : n < N) :
    concreteL2RawTruncation x N n = x.1 n := by
  unfold concreteL2RawTruncation
  exact if_pos hn

/-- Outside the cutoff, raw truncation is zero. -/
theorem concrete_l2_raw_truncation_eq_zero_of_not_lt
    (x : ConcreteL2RealSequence) (N n : ℕ) (hn : ¬ n < N) :
    concreteL2RawTruncation x N n = 0 := by
  unfold concreteL2RawTruncation
  exact if_neg hn

/-- The zero cutoff is pointwise zero. -/
theorem concrete_l2_raw_truncation_zero_cutoff
    (x : ConcreteL2RealSequence) (n : ℕ) :
    concreteL2RawTruncation x 0 n = 0 := by
  exact concrete_l2_raw_truncation_eq_zero_of_not_lt x 0 n (Nat.not_lt_zero n)

/-- Target: raw truncations should define concrete `l2` carrier points. -/
def concreteL2RawTruncationSummabilityTarget : Prop :=
  ∀ x : ConcreteL2RealSequence,
  ∀ N : ℕ,
    Summable fun n : ℕ => (concreteL2RawTruncation x N n) ^ 2

/-- Target: raw truncations should have finite support. -/
def concreteL2RawTruncationFiniteSupportTarget : Prop :=
  ∀ x : ConcreteL2RealSequence,
  ∀ N : ℕ,
    ({n : ℕ | concreteL2RawTruncation x N n ≠ 0} : Set ℕ).Finite

/--
Target: raw truncations of a diagonal-domain point should stay in the diagonal
domain after they are promoted to the `l2` carrier.
-/
def concreteL2RawTruncationDiagonalDomainTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
  ∀ N : ℕ,
    ∀ hsumm : Summable fun n : ℕ => (concreteL2RawTruncation x.1 N n) ^ 2,
      ConcreteL2DiagonalDomain
        (⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence)

/-- Target: truncation should produce finite-support canonical graph pairs. -/
def concreteL2RawTruncationFiniteSupportGraphTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
  ∀ N : ℕ,
  ∀ hsumm : Summable fun n : ℕ => (concreteL2RawTruncation x.1 N n) ^ 2,
  ∀ hdom : ConcreteL2DiagonalDomain
      (⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence),
    let xN : ConcreteL2DiagonalDomainCarrier :=
      ⟨(⟨concreteL2RawTruncation x.1 N, hsumm⟩ : ConcreteL2RealSequence), hdom⟩
    ((xN.1, concreteL2DiagonalActionL2 xN) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier)

/--
Target: the truncation-derived canonical graph sequence should converge in the
named graph-norm topology.
-/
def concreteL2RawTruncationGraphNormConvergenceTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
    concreteL2MathlibSpectralAuditR2GraphNormDomainSequenceTarget x

/--
The full truncation-to-domain-sequence obligation bundles the four missing
analytic facts needed before the global graph-norm density theorem can be
closed constructively.
-/
def concreteL2RawTruncationToDomainSequenceObligation : Prop :=
  concreteL2RawTruncationSummabilityTarget ∧
  concreteL2RawTruncationFiniteSupportTarget ∧
  concreteL2RawTruncationDiagonalDomainTarget ∧
  concreteL2RawTruncationFiniteSupportGraphTarget ∧
  concreteL2RawTruncationGraphNormConvergenceTarget

/-- Surface for the raw truncation targets in the graph-norm density lane. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurface where
  domainSequenceBridgeReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurfaceReady
  rawTruncation : ConcreteL2RealSequence → ℕ → ℕ → ℝ
  rawInsideCutoffLaw :
    ∀ x : ConcreteL2RealSequence,
    ∀ N n : ℕ,
      n < N → concreteL2RawTruncation x N n = x.1 n
  rawOutsideCutoffLaw :
    ∀ x : ConcreteL2RealSequence,
    ∀ N n : ℕ,
      ¬ n < N → concreteL2RawTruncation x N n = 0
  truncationObligation : Prop
  boundaryNotTruncationSummabilityTheorem : Prop
  boundaryNotTruncationGraphNormConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the raw truncation targets in the graph-norm density lane. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurface :=
  { domainSequenceBridgeReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_domain_sequence_bridge_surface_ready
    rawTruncation := concreteL2RawTruncation
    rawInsideCutoffLaw := concrete_l2_raw_truncation_eq_of_lt
    rawOutsideCutoffLaw := concrete_l2_raw_truncation_eq_zero_of_not_lt
    truncationObligation := concreteL2RawTruncationToDomainSequenceObligation
    boundaryNotTruncationSummabilityTheorem := True
    boundaryNotTruncationGraphNormConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the raw truncation targets in the graph-norm density lane. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurfaceReady ∧
  (∀ x : ConcreteL2RealSequence,
    ∀ N n : ℕ,
      n < N → concreteL2RawTruncation x N n = x.1 n) ∧
  (∀ x : ConcreteL2RealSequence,
    ∀ N n : ℕ,
      ¬ n < N → concreteL2RawTruncation x N n = 0)

/-- Readiness theorem for the raw truncation targets in the graph-norm density lane. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_targets_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationTargetsSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_domain_sequence_bridge_surface_ready,
    concrete_l2_raw_truncation_eq_of_lt,
    concrete_l2_raw_truncation_eq_zero_of_not_lt⟩

end

end MathlibAnalytic
end MGAP4D