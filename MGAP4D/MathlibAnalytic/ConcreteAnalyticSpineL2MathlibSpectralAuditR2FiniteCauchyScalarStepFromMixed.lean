import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Scalar Cauchy induction step from the mixed-term estimate.

For the Finset-induction proof of finite Cauchy, the only nontrivial algebraic
part is the mixed term.  Once

`2 * A * x * y ≤ B * y^2 + C * x^2`

is available, the enlarged square inequality follows by pure ring algebra.
-/
theorem concrete_l2_finite_cauchy_scalar_step_from_mixed
    {A B C x y : ℝ}
    (hbase : A ^ 2 ≤ B * C)
    (hmix : (2 : ℝ) * A * x * y ≤ B * y ^ 2 + C * x ^ 2) :
    (A + x * y) ^ 2 ≤ (B + x ^ 2) * (C + y ^ 2) := by
  have hsum : A ^ 2 + (2 : ℝ) * A * x * y + (x * y) ^ 2 ≤
      B * C + (B * y ^ 2 + C * x ^ 2) + (x * y) ^ 2 := by
    nlinarith
  have hleft : (A + x * y) ^ 2 =
      A ^ 2 + (2 : ℝ) * A * x * y + (x * y) ^ 2 := by
    ring
  have hright :
      B * C + (B * y ^ 2 + C * x ^ 2) + (x * y) ^ 2 =
        (B + x ^ 2) * (C + y ^ 2) := by
    ring
  rw [hleft]
  exact hsum.trans_eq hright

/--
Package: the scalar step follows from the scalar mixed estimate.
-/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixed : Prop :=
  ∀ A B C x y : ℝ,
    A ^ 2 ≤ B * C →
    (2 : ℝ) * A * x * y ≤ B * y ^ 2 + C * x ^ 2 →
      (A + x * y) ^ 2 ≤ (B + x ^ 2) * (C + y ^ 2)

/-- The scalar-step-from-mixed package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step_from_mixed :
    concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixed := by
  intro A B C x y hbase hmix
  exact concrete_l2_finite_cauchy_scalar_step_from_mixed hbase hmix

/--
Surface for the algebraic bridge from mixed-term control to the scalar induction
step.
-/
structure ConcreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurface where
  inductionFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurfaceReady
  stepFromMixed : concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixed
  boundaryNotMixedTermTheorem : Prop
  boundaryNotFullScalarStep : Prop
  boundaryNotFinitePrefixSquareCauchy : Prop
  boundaryNotSummedCauchy : Prop

/-- Concrete surface for scalar-step-from-mixed. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurface :
    ConcreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurface :=
  { inductionFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_frontier_surface_ready
    stepFromMixed :=
      concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step_from_mixed
    boundaryNotMixedTermTheorem := True
    boundaryNotFullScalarStep := True
    boundaryNotFinitePrefixSquareCauchy := True
    boundaryNotSummedCauchy := True }

/-- Readiness predicate for scalar-step-from-mixed surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyInductionFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixed

/-- Readiness theorem for scalar-step-from-mixed surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step_from_mixed_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_induction_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step_from_mixed⟩

end

end MathlibAnalytic
end MGAP4D
