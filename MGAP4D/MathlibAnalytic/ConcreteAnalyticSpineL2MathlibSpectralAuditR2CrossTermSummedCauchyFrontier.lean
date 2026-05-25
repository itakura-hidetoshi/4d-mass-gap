import Mathlib.Topology.Algebra.InfiniteSum.Real
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2SummedSqrtEnergyCauchy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Cross-term summed Cauchy frontier.

The pointwise Cauchy estimate for the cross term is already available:
`cross(p,q,n) ≤ sqrt(e_p n) sqrt(e_q n)`.  Since the cross term can have signs,
we do not use the nonnegative comparison theorem directly on the cross term
here.  Instead, this frontier isolates the exact next analytic requirement:
showing that the cross-term series has a summable/tsum interpretation compatible
with the pointwise upper bound.
-/
def concreteL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurfaceReady

/-- Readiness theorem for the cross-term summed Cauchy frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_frontier_ready :
    concreteL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy_surface_ready

/-- Target: summability of the cross-term series. -/
def concreteL2MathlibSpectralAuditR2CrossTermSummableTarget : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ => concreteL2GraphPairCrossTerm p q n

/-- Target: summed Cauchy for the cross-term series. -/
def concreteL2MathlibSpectralAuditR2CrossTermSummedCauchyTargetV2 : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) ≤
      Real.sqrt (concreteL2CompletedGraphEnergy p) *
        Real.sqrt (concreteL2CompletedGraphEnergy q)

/--
The pointwise cross-term Cauchy estimate inherited from the pointwise Cauchy
leaf.
-/
def concreteL2MathlibSpectralAuditR2CrossTermPointwiseCauchyInherited : Prop :=
  concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchy

/-- The inherited pointwise cross-term Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_pointwise_cauchy_inherited :
    concreteL2MathlibSpectralAuditR2CrossTermPointwiseCauchyInherited := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_pointwise_cauchy

/-- Surface for cross-term summed Cauchy frontier. -/
structure ConcreteL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurface where
  summedSqrtReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurfaceReady
  pointwiseCrossCauchy : concreteL2MathlibSpectralAuditR2CrossTermPointwiseCauchyInherited
  crossTermSummableTarget : Prop
  crossTermSummedCauchyTarget : Prop
  boundaryNotCrossTermSummability : Prop
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete cross-term summed Cauchy frontier surface. -/
def concreteL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurface :=
  { summedSqrtReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy_surface_ready
    pointwiseCrossCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_cross_term_pointwise_cauchy_inherited
    crossTermSummableTarget :=
      concreteL2MathlibSpectralAuditR2CrossTermSummableTarget
    crossTermSummedCauchyTarget :=
      concreteL2MathlibSpectralAuditR2CrossTermSummedCauchyTargetV2
    boundaryNotCrossTermSummability := True
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for cross-term summed Cauchy frontier. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontier ∧
  concreteL2MathlibSpectralAuditR2CrossTermPointwiseCauchyInherited ∧
  concreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchy

/-- Readiness theorem for cross-term summed Cauchy frontier. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_frontier_ready,
    concrete_l2_mathlib_spectral_audit_r2_cross_term_pointwise_cauchy_inherited,
    concrete_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy⟩

end

end MathlibAnalytic
end MGAP4D
