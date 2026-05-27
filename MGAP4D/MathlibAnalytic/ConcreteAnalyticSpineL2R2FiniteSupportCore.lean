import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2FiniteSupportCore
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenselyDefinedOperator

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- R2-facing finite-support core surface.

This is a thin wrapper around the existing concrete `l2` finite-support core
surface.  It brings the finite-support core into the R2 physical spectral
promotion chain without claiming graph-norm density, closedness,
essential self-adjointness, PVM construction, an exact `33/20` atom, or positive
spectral weight. -/
structure ConcreteL2R2FiniteSupportCoreSurface where
  denselyDefinedOperatorReady : concreteL2R2DenselyDefinedOperatorReady
  inheritedFiniteSupportCoreSurfaceReady : concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady
  coreNonempty : Nonempty ConcreteL2DiagonalFiniteSupportDomainCarrier
  coreGraphNonempty : concreteL2FiniteSupportCoreSurface.coreGraphCarrier.Nonempty
  zeroCoreGraphMem :
    (concreteL2RealZero, concreteL2RealZero) ∈
      concreteL2FiniteSupportCoreSurface.coreGraphCarrier
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotEssentialSelfAdjointness : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomThirtyThreeTwentieth : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2 finite-support core surface. -/
def concreteL2R2FiniteSupportCoreSurface :
    ConcreteL2R2FiniteSupportCoreSurface :=
  { denselyDefinedOperatorReady :=
      concrete_analytic_spine_l2_r2_densely_defined_operator_ready
    inheritedFiniteSupportCoreSurfaceReady :=
      concrete_analytic_spine_l2_finite_support_core_surface_ready
    coreNonempty := concrete_l2_diagonal_finite_support_domain_nonempty
    coreGraphNonempty := concrete_l2_finite_support_core_graph_nonempty
    zeroCoreGraphMem := concrete_l2_finite_support_core_zero_graph_mem
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotEssentialSelfAdjointness := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomThirtyThreeTwentieth := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the R2 finite-support core surface. -/
def concreteL2R2FiniteSupportCoreReady : Prop :=
  concreteL2R2DenselyDefinedOperatorReady ∧
  concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady ∧
  Nonempty ConcreteL2DiagonalFiniteSupportDomainCarrier ∧
  concreteL2FiniteSupportCoreSurface.coreGraphCarrier.Nonempty ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotEssentialSelfAdjointness ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotSelfAdjointnessTheorem ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotPVMConstruction ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotExactAtomThirtyThreeTwentieth ∧
  concreteL2R2FiniteSupportCoreSurface.boundaryNotPositiveSpectralWeight

/-- The R2 finite-support core surface is ready.

This theorem exposes the finite-support core into the R2 promotion chain.  It is
still only a core-surface theorem: it does not assert graph-norm density,
closedness, essential self-adjointness, self-adjointness, PVM construction, the
exact `33/20` atom, positive spectral weight, or the physical Yang--Mills
Hamiltonian. -/
theorem concrete_analytic_spine_l2_r2_finite_support_core_ready :
    concreteL2R2FiniteSupportCoreReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_densely_defined_operator_ready,
    concrete_analytic_spine_l2_finite_support_core_surface_ready,
    concrete_l2_diagonal_finite_support_domain_nonempty,
    concrete_l2_finite_support_core_graph_nonempty,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
