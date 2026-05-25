import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySquareTarget

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Finite-prefix dot product nonnegativity.

The finite-prefix square-root energy vectors are pointwise nonnegative, hence
so is their finite dot product.  This is one of the two ingredients needed to
turn the squared Cauchy inequality into the usual sqrt-form finite-prefix
Cauchy inequality.
-/
theorem concrete_l2_finite_prefix_dot_nonneg
    (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ) :
    0 ≤ Finset.sum s
      (fun n : ℕ =>
        concreteL2FinitePrefixSqrtEnergyLeft p s n *
          concreteL2FinitePrefixSqrtEnergyRight q s n) := by
  refine Finset.sum_nonneg ?_
  intro n hn
  exact mul_nonneg
    (concrete_l2_finite_prefix_sqrt_energy_left_nonneg p s n)
    (concrete_l2_finite_prefix_sqrt_energy_right_nonneg q s n)

/-- Finite-prefix dot product nonnegativity package. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixDotNonneg : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ),
    0 ≤ Finset.sum s
      (fun n : ℕ =>
        concreteL2FinitePrefixSqrtEnergyLeft p s n *
          concreteL2FinitePrefixSqrtEnergyRight q s n)

/-- The finite-prefix dot product nonnegativity package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_dot_nonneg :
    concreteL2MathlibSpectralAuditR2FinitePrefixDotNonneg := by
  exact concrete_l2_finite_prefix_dot_nonneg

/--
Finite-prefix dot-nonneg surface.
-/
structure ConcreteL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurface where
  squareFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurfaceReady
  dotNonneg : concreteL2MathlibSpectralAuditR2FinitePrefixDotNonneg
  boundaryNotSquareCauchy : Prop
  boundaryNotFinitePrefixCauchy : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete finite-prefix dot-nonneg surface. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurface :
    ConcreteL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurface :=
  { squareFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_square_frontier_surface_ready
    dotNonneg :=
      concrete_l2_mathlib_spectral_audit_r2_finite_prefix_dot_nonneg
    boundaryNotSquareCauchy := True
    boundaryNotFinitePrefixCauchy := True
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the finite-prefix dot-nonneg surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FinitePrefixDotNonneg

/-- Readiness theorem for the finite-prefix dot-nonneg surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_dot_nonneg_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_square_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_prefix_dot_nonneg⟩

end

end MathlibAnalytic
end MGAP4D
