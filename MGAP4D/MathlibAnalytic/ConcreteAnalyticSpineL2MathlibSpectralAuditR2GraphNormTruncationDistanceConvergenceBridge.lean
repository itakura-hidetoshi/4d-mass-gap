import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructor

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Metric ε-form of the remaining truncation convergence theorem.

For each diagonal-domain point, the graph-norm distance from the canonical graph
of its finite truncation to the target canonical graph eventually becomes smaller
than every positive `ε`.
-/
def concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
  ∀ ε : ℝ,
    0 < ε →
      ∀ᶠ N in Filter.atTop,
        concreteL2GraphNormDistanceCandidate
          (concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
            (concreteL2RawTruncationDomainSequence x) N)
          (x.1, concreteL2DiagonalActionL2 x) < ε

/--
The metric ε-form of truncation convergence implies the named graph-norm
topological convergence target, via mathlib's `Metric.tendsto_nhds`.
-/
theorem concrete_l2_raw_truncation_canonical_graph_convergence_of_distance_epsilon
    (hε : concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget) :
    concreteL2RawTruncationCanonicalGraphConvergenceTarget := by
  intro x
  letI : PseudoMetricSpace ConcreteL2GraphPairSpace := concreteL2GraphNormPseudoMetricSpace
  exact (Metric.tendsto_nhds).2 (by
    intro ε hεpos
    filter_upwards [hε x ε hεpos] with N hN
    rw [concrete_l2_graph_norm_pseudo_metric_space_dist_eq]
    exact hN)

/--
The metric ε-form also implies the full remaining convergence-only frontier.
-/
theorem concrete_l2_remaining_convergence_only_of_distance_epsilon
    (hε : concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget) :
    concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget := by
  exact concrete_l2_remaining_convergence_only_of_canonical_graph_convergence
    (concrete_l2_raw_truncation_canonical_graph_convergence_of_distance_epsilon hε)

/--
The metric ε-form implies the precise graph-norm finite-support density target.
-/
theorem concrete_l2_graph_norm_precise_density_target_of_distance_epsilon
    (hε : concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_graph_norm_precise_density_target_of_remaining_convergence_only
    (concrete_l2_remaining_convergence_only_of_distance_epsilon hε)

/-- Surface for the distance-to-topology convergence bridge. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurface where
  truncationDomainSequenceConstructorReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurfaceReady
  distanceEpsilonTarget : Prop
  distanceEpsilonImpliesCanonicalGraphConvergence :
    distanceEpsilonTarget → concreteL2RawTruncationCanonicalGraphConvergenceTarget
  distanceEpsilonImpliesRemainingConvergenceOnly :
    distanceEpsilonTarget → concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget
  distanceEpsilonImpliesPreciseDensity :
    distanceEpsilonTarget → concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryNotDistanceEpsilonTheorem : Prop
  boundaryNotTailEstimateTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the distance-to-topology convergence bridge. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurface :=
  { truncationDomainSequenceConstructorReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_domain_sequence_constructor_surface_ready
    distanceEpsilonTarget :=
      concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget
    distanceEpsilonImpliesCanonicalGraphConvergence :=
      concrete_l2_raw_truncation_canonical_graph_convergence_of_distance_epsilon
    distanceEpsilonImpliesRemainingConvergenceOnly :=
      concrete_l2_remaining_convergence_only_of_distance_epsilon
    distanceEpsilonImpliesPreciseDensity :=
      concrete_l2_graph_norm_precise_density_target_of_distance_epsilon
    boundaryNotDistanceEpsilonTheorem := True
    boundaryNotTailEstimateTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the distance-to-topology convergence bridge. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurfaceReady ∧
  (concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget →
    concreteL2RawTruncationCanonicalGraphConvergenceTarget) ∧
  (concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/-- Readiness theorem for the distance-to-topology convergence bridge. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_distance_convergence_bridge_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_domain_sequence_constructor_surface_ready,
    concrete_l2_raw_truncation_canonical_graph_convergence_of_distance_epsilon,
    concrete_l2_graph_norm_precise_density_target_of_distance_epsilon⟩

end

end MathlibAnalytic
end MGAP4D