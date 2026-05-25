import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Finite-prefix Cauchy square target.

For the finite vectors prepared in the previous frontier, the core algebraic
claim is the squared Cauchy inequality.  This square form is the cleanest next
step because it avoids monotonicity of `sqrt` until the final passage.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareTarget : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ),
    (Finset.sum s
        (fun n : ℕ =>
          concreteL2FinitePrefixSqrtEnergyLeft p s n *
            concreteL2FinitePrefixSqrtEnergyRight q s n)) ^ 2 ≤
      (Finset.sum s
          (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyLeft p s n ^ 2)) *
        (Finset.sum s
          (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyRight q s n ^ 2))

/--
Finite-prefix dot-product nonnegativity target.

Because the finite-prefix vectors are pointwise nonnegative, their finite dot
product is nonnegative.  Together with the square target this gives the sqrt
form of finite-prefix Cauchy.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixDotNonnegTarget : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ),
    0 ≤ Finset.sum s
      (fun n : ℕ =>
        concreteL2FinitePrefixSqrtEnergyLeft p s n *
          concreteL2FinitePrefixSqrtEnergyRight q s n)

/--
Finite-prefix square-to-sqrt bridge target.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixSquareToSqrtBridgeTarget : Prop :=
  concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareTarget ∧
  concreteL2MathlibSpectralAuditR2FinitePrefixDotNonnegTarget

/--
Finite-prefix Cauchy square frontier.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurfaceReady

/-- Readiness theorem for the finite-prefix Cauchy square frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_square_frontier_ready :
    concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_frontier_surface_ready

/--
Structured surface for the square-form finite-prefix Cauchy obligation.
-/
structure ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurface where
  finitePrefixFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurfaceReady
  squareTarget : Prop
  dotNonnegTarget : Prop
  squareToSqrtBridgeTarget : Prop
  boundaryNotFinitePrefixCauchy : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete square-form finite-prefix Cauchy frontier surface. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurface :=
  { finitePrefixFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_frontier_surface_ready
    squareTarget := concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareTarget
    dotNonnegTarget := concreteL2MathlibSpectralAuditR2FinitePrefixDotNonnegTarget
    squareToSqrtBridgeTarget :=
      concreteL2MathlibSpectralAuditR2FinitePrefixSquareToSqrtBridgeTarget
    boundaryNotFinitePrefixCauchy := True
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the square-form finite-prefix Cauchy frontier. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontier

/-- Readiness theorem for the square-form finite-prefix Cauchy frontier. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_square_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySquareFrontierSurfaceReady := by
  exact concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_square_frontier_ready

end

end MathlibAnalytic
end MGAP4D
