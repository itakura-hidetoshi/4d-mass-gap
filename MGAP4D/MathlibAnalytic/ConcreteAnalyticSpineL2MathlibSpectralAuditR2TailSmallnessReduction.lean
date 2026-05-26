import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2PrefixDeficitSmall

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The final comparison still needed for the energy route to graph-norm density.

For each diagonal-domain point and cutoff, the completed graph energy of the raw
truncation graph error should be bounded by the target graph's completed-energy
prefix deficit.  Once this comparison is proved, the prefix-deficit smallness
already proved in the previous leaf gives the full energy-ε tail-smallness
target.
-/
def concreteL2RawTruncationGraphErrorEnergyLeTargetPrefixDeficit : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
  ∀ N : ℕ,
    concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N) ≤
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) -
        Finset.sum (Finset.range N)
          (fun n : ℕ =>
            concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n)

/--
Tail-smallness follows from the truncation-error/prefix-deficit comparison.

This is the clean order-theoretic closure step: the prefix-deficit is eventually
below `ε^2`, and the truncation-error completed energy is bounded by that
deficit, so the truncation-error energy is eventually below `ε^2`.
-/
theorem concrete_l2_raw_truncation_energy_epsilon_of_error_le_prefix_deficit
    (hcmp : concreteL2RawTruncationGraphErrorEnergyLeTargetPrefixDeficit) :
    concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget := by
  intro x ε hε
  have hsmall :=
    concrete_l2_diagonal_target_graph_prefix_deficit_eventually_lt_eps_sq x ε hε
  filter_upwards [hsmall] with N hN
  exact lt_of_le_of_lt (hcmp x N) hN

/--
The final comparison would close the precise graph-norm finite-support density
target through the existing energy-ε bridge.
-/
theorem concrete_l2_precise_density_of_error_le_prefix_deficit
    (hcmp : concreteL2RawTruncationGraphErrorEnergyLeTargetPrefixDeficit) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_graph_norm_precise_density_target_of_energy_epsilon
    (concrete_l2_raw_truncation_energy_epsilon_of_error_le_prefix_deficit hcmp)

/--
Reduction package: the only remaining analytic obligation for tail-smallness is
now the truncation-error/prefix-deficit comparison.
-/
def concreteL2MathlibSpectralAuditR2TailSmallnessReductionPackage : Prop :=
  concreteL2RawTruncationGraphErrorEnergyLeTargetPrefixDeficit →
    concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget

/-- The tail-smallness reduction package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_tail_smallness_reduction_package_ready :
    concreteL2MathlibSpectralAuditR2TailSmallnessReductionPackage := by
  exact concrete_l2_raw_truncation_energy_epsilon_of_error_le_prefix_deficit

/--
Boundary retained after the reduction.

This file does not prove the comparison itself.  It proves that the comparison
is sufficient and isolates it as the next exact `tsum`/tail theorem.
-/
def concreteL2MathlibSpectralAuditR2TailSmallnessReductionBoundaryHeld : Prop :=
  True

/-- Surface for the tail-smallness reduction. -/
structure ConcreteL2MathlibSpectralAuditR2TailSmallnessReductionSurface where
  prefixDeficitSmallReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2PrefixDeficitSmallSurfaceReady
  comparisonTarget : Prop
  comparisonImpliesEnergyEpsilon :
    comparisonTarget → concreteL2RawTruncationCanonicalGraphEnergyEpsilonConvergenceTarget
  comparisonImpliesPreciseDensity :
    comparisonTarget →
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  reductionPackage : concreteL2MathlibSpectralAuditR2TailSmallnessReductionPackage
  boundaryHeld : concreteL2MathlibSpectralAuditR2TailSmallnessReductionBoundaryHeld
  boundaryNotComparisonTheorem : Prop
  boundaryNotExactTailTsumTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the tail-smallness reduction. -/
def concreteL2MathlibSpectralAuditR2TailSmallnessReductionSurface :
    ConcreteL2MathlibSpectralAuditR2TailSmallnessReductionSurface :=
  { prefixDeficitSmallReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_prefix_deficit_small_surface_ready
    comparisonTarget :=
      concreteL2RawTruncationGraphErrorEnergyLeTargetPrefixDeficit
    comparisonImpliesEnergyEpsilon :=
      concrete_l2_raw_truncation_energy_epsilon_of_error_le_prefix_deficit
    comparisonImpliesPreciseDensity :=
      concrete_l2_precise_density_of_error_le_prefix_deficit
    reductionPackage :=
      concrete_l2_mathlib_spectral_audit_r2_tail_smallness_reduction_package_ready
    boundaryHeld := True.intro
    boundaryNotComparisonTheorem := True
    boundaryNotExactTailTsumTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the tail-smallness reduction surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessReductionSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2PrefixDeficitSmallSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2TailSmallnessReductionPackage ∧
  concreteL2MathlibSpectralAuditR2TailSmallnessReductionBoundaryHeld

/-- Readiness theorem for the tail-smallness reduction surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_smallness_reduction_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessReductionSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_prefix_deficit_small_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_tail_smallness_reduction_package_ready,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
