import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR1FiniteStatus
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrder

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Input package for the next tail-smallness theorem.

After the finite-status handoff and the finite-prefix order bound, the concrete
`l2` graph-norm density lane has the three analytic ingredients needed for the
next tail estimate:

* completed graph-energy prefix convergence;
* truncation-error prefix energy is zero on `Finset.range N`;
* every finite graph-energy prefix is bounded by completed graph energy.

This package is deliberately an input surface.  It does not yet assert the full
completed-energy tail-smallness theorem.
-/
def concreteL2MathlibSpectralAuditR2TailSmallnessInput : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR1FiniteStatusSurfaceReady ∧
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurfaceReady ∧
  concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurfaceReady ∧
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurfaceReady

/-- The tail-smallness input package is ready from the current main spine. -/
theorem concrete_l2_mathlib_spectral_audit_r2_tail_smallness_input_ready :
    concreteL2MathlibSpectralAuditR2TailSmallnessInput := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r1_finite_status_surface_ready,
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_energy_prefix_limit_surface_ready,
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_prefix_zero_surface_ready,
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_energy_prefix_order_surface_ready⟩

/--
The concrete theorem still needed to close graph-norm density through the energy
route: completed graph energy of the raw truncation graph error is eventually
less than `ε^2`.
-/
def concreteL2MathlibSpectralAuditR2TailSmallnessTarget : Prop :=
  concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget

/--
If the tail-smallness target is supplied, the existing energy-ε bridge closes
the precise graph-norm finite-support density target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_precise_density_of_tail_smallness
    (hTail : concreteL2MathlibSpectralAuditR2TailSmallnessTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_graph_norm_precise_density_target_of_energy_epsilon hTail

/--
Boundary retained after bundling tail-smallness inputs.

The input package prepares the next theorem but does not itself discharge the
completed-energy tail estimate, graph-norm core theorem, closed operator,
self-adjointness, PVM construction, exact-atom derivation, or positive spectral
weight.
-/
def concreteL2MathlibSpectralAuditR2TailSmallnessInputBoundaryHeld : Prop :=
  True

/-- Surface for the tail-smallness input package. -/
structure ConcreteL2MathlibSpectralAuditR2TailSmallnessInputSurface where
  finiteStatusReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR1FiniteStatusSurfaceReady
  prefixLimitReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurfaceReady
  prefixZeroReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurfaceReady
  prefixOrderReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrderSurfaceReady
  tailInputReady : concreteL2MathlibSpectralAuditR2TailSmallnessInput
  tailSmallnessTarget : Prop
  tailSmallnessImpliesPreciseDensity :
    tailSmallnessTarget →
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryHeld : concreteL2MathlibSpectralAuditR2TailSmallnessInputBoundaryHeld
  boundaryNotTailSmallnessTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the tail-smallness input package. -/
def concreteL2MathlibSpectralAuditR2TailSmallnessInputSurface :
    ConcreteL2MathlibSpectralAuditR2TailSmallnessInputSurface :=
  { finiteStatusReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r1_finite_status_surface_ready
    prefixLimitReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_energy_prefix_limit_surface_ready
    prefixZeroReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_prefix_zero_surface_ready
    prefixOrderReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_energy_prefix_order_surface_ready
    tailInputReady :=
      concrete_l2_mathlib_spectral_audit_r2_tail_smallness_input_ready
    tailSmallnessTarget :=
      concreteL2MathlibSpectralAuditR2TailSmallnessTarget
    tailSmallnessImpliesPreciseDensity :=
      concrete_l2_mathlib_spectral_audit_r2_precise_density_of_tail_smallness
    boundaryHeld := True.intro
    boundaryNotTailSmallnessTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the tail-smallness input surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessInputSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2TailSmallnessInput ∧
  (concreteL2MathlibSpectralAuditR2TailSmallnessTarget →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget) ∧
  concreteL2MathlibSpectralAuditR2TailSmallnessInputBoundaryHeld

/-- Readiness theorem for the tail-smallness input surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_smallness_input_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessInputSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_tail_smallness_input_ready,
    concrete_l2_mathlib_spectral_audit_r2_precise_density_of_tail_smallness,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
