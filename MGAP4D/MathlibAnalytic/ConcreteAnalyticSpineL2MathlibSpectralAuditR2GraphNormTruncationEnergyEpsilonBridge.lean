import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The graph-pair error between a raw truncation graph and the target graph. -/
def concreteL2RawTruncationGraphError
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) : ConcreteL2GraphPairSpace :=
  concreteL2GraphPairSub
    (concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
      (concreteL2RawTruncationDomainSequence x) N)
    (x.1, concreteL2DiagonalActionL2 x)

/--
Energy ε-form of the remaining truncation convergence theorem.

This is the square-energy version of distance convergence.  By `Real.sqrt_lt'`,
it is enough to prove that the completed graph energy of the truncation error is
eventually below `ε^2`.
-/
def concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
  ∀ ε : ℝ,
    0 < ε →
      ∀ᶠ N in Filter.atTop,
        concreteL2CompletedGraphEnergy
          (concreteL2RawTruncationGraphError x N) < ε ^ 2

/--
The energy ε-form implies the distance ε-form, using mathlib's
`Real.sqrt_lt'`.
-/
theorem concrete_l2_raw_truncation_distance_epsilon_of_energy_epsilon
    (hE : concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget) :
    concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget := by
  intro x ε hεpos
  filter_upwards [hE x ε hεpos] with N hN
  unfold concreteL2GraphNormDistanceCandidate
  unfold concreteL2GraphNormCandidate
  unfold concreteL2RawTruncationGraphError at hN
  exact (Real.sqrt_lt' hεpos).2 hN

/--
The energy ε-form implies canonical graph convergence.
-/
theorem concrete_l2_raw_truncation_canonical_graph_convergence_of_energy_epsilon
    (hE : concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget) :
    concreteL2RawTruncationCanonicalGraphConvergenceTarget := by
  exact concrete_l2_raw_truncation_canonical_graph_convergence_of_distance_epsilon
    (concrete_l2_raw_truncation_distance_epsilon_of_energy_epsilon hE)

/--
The energy ε-form implies the precise graph-norm finite-support density target.
-/
theorem concrete_l2_graph_norm_precise_density_target_of_energy_epsilon
    (hE : concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_graph_norm_precise_density_target_of_distance_epsilon
    (concrete_l2_raw_truncation_distance_epsilon_of_energy_epsilon hE)

/-- Surface reducing graph-norm convergence to completed graph-energy ε-control. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurface where
  distanceConvergenceBridgeReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurfaceReady
  energyEpsilonTarget : Prop
  energyEpsilonImpliesDistanceEpsilon :
    energyEpsilonTarget → concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget
  energyEpsilonImpliesCanonicalGraphConvergence :
    energyEpsilonTarget → concreteL2RawTruncationCanonicalGraphConvergenceTarget
  energyEpsilonImpliesPreciseDensity :
    energyEpsilonTarget → concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryNotEnergyEpsilonTheorem : Prop
  boundaryNotTailEstimateTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface reducing graph-norm convergence to completed graph-energy ε-control. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurface :=
  { distanceConvergenceBridgeReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_distance_convergence_bridge_surface_ready
    energyEpsilonTarget :=
      concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget
    energyEpsilonImpliesDistanceEpsilon :=
      concrete_l2_raw_truncation_distance_epsilon_of_energy_epsilon
    energyEpsilonImpliesCanonicalGraphConvergence :=
      concrete_l2_raw_truncation_canonical_graph_convergence_of_energy_epsilon
    energyEpsilonImpliesPreciseDensity :=
      concrete_l2_graph_norm_precise_density_target_of_energy_epsilon
    boundaryNotEnergyEpsilonTheorem := True
    boundaryNotTailEstimateTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the energy ε bridge. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDistanceConvergenceBridgeSurfaceReady ∧
  (concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget →
    concreteL2RawTruncationCanonicalGraphDistanceEpsilonConvergenceTarget) ∧
  (concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/-- Readiness theorem for the energy ε bridge. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_energy_epsilon_bridge_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationEnergyEpsilonBridgeSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_distance_convergence_bridge_surface_ready,
    concrete_l2_raw_truncation_distance_epsilon_of_energy_epsilon,
    concrete_l2_graph_norm_precise_density_target_of_energy_epsilon⟩

end

end MathlibAnalytic
end MGAP4D