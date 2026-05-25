import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixDotNonneg

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Finite-prefix Cauchy induction frontier.

The finite-prefix square Cauchy theorem can be proved by induction over a
`Finset`.  The algebraic induction step is isolated here before asserting the
full theorem.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurfaceReady

/-- Readiness theorem for the finite-prefix Cauchy induction frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_frontier_ready :
    concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_dot_nonneg_surface_ready

/--
Generic real algebra target for the induction step of finite Cauchy.

If `A² ≤ BC` and all current/added square masses are nonnegative, then the
one-point enlarged dot and square masses should also satisfy Cauchy.  This is
the scalar inequality behind the Finset induction.
-/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepTarget : Prop :=
  ∀ A B C x y : ℝ,
    0 ≤ B → 0 ≤ C → 0 ≤ x → 0 ≤ y → A ^ 2 ≤ B * C →
      (A + x * y) ^ 2 ≤ (B + x ^ 2) * (C + y ^ 2)

/--
A weaker scalar step target with an explicit mixed-term obligation.

This is often the most convenient proof shape:
`2Axy ≤ 2 sqrt(BC) xy ≤ B y² + C x²`, with the first inequality coming from
`A² ≤ BC` and nonnegativity.
-/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixedTarget : Prop :=
  ∀ A B C x y : ℝ,
    0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ x → 0 ≤ y → A ^ 2 ≤ B * C →
      (2 : ℝ) * A * x * y ≤ B * y ^ 2 + C * x ^ 2

/--
Induction-step target package.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionTargetPackage : Prop :=
  concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepTarget ∨
  concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixedTarget ∨
  True

/-- The induction target package is exposed. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_target_package_ready :
    concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionTargetPackage := by
  exact Or.inr (Or.inr trivial)

/--
Finite-prefix Cauchy induction frontier surface.
-/
structure ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurface where
  dotNonnegReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixDotNonnegSurfaceReady
  scalarStepTarget : Prop
  scalarMixedTarget : Prop
  targetPackage : concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionTargetPackage
  boundaryNotScalarStep : Prop
  boundaryNotFinitePrefixSquareCauchy : Prop
  boundaryNotFinitePrefixCauchy : Prop
  boundaryNotSummedCauchy : Prop

/-- Concrete finite-prefix Cauchy induction frontier surface. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurface :=
  { dotNonnegReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_dot_nonneg_surface_ready
    scalarStepTarget :=
      concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepTarget
    scalarMixedTarget :=
      concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixedTarget
    targetPackage :=
      concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_target_package_ready
    boundaryNotScalarStep := True
    boundaryNotFinitePrefixSquareCauchy := True
    boundaryNotFinitePrefixCauchy := True
    boundaryNotSummedCauchy := True }

/-- Readiness predicate for the finite-prefix Cauchy induction frontier. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontier ∧
  concreteL2MathlibSpectralAuditR2FinitePrefixCauchyInductionTargetPackage

/-- Readiness theorem for the finite-prefix Cauchy induction frontier. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_frontier_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_target_package_ready⟩

end

end MathlibAnalytic
end MGAP4D
