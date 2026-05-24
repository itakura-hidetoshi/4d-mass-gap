import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixed

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The elementary inequality `2uv ≤ u² + v²` over the reals.
-/
theorem concrete_l2_two_mul_le_sq_add_sq (u v : ℝ) :
    (2 : ℝ) * u * v ≤ u ^ 2 + v ^ 2 := by
  have hsq : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
  nlinarith

/--
Scalar mixed-term estimate for the finite Cauchy induction step.

Assuming `0 ≤ A`, `0 ≤ B`, `0 ≤ C`, `0 ≤ x`, `0 ≤ y`, and `A² ≤ BC`, the
mixed term in the one-point Cauchy induction step is controlled by
`B y² + C x²`.
-/
theorem concrete_l2_finite_cauchy_scalar_mixed
    {A B C x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hbase : A ^ 2 ≤ B * C) :
    (2 : ℝ) * A * x * y ≤ B * y ^ 2 + C * x ^ 2 := by
  have hBC_nonneg : 0 ≤ B * C := mul_nonneg hB hC
  have hA_le_sqrt : A ≤ Real.sqrt (B * C) := by
    have hsqrt_sq : (Real.sqrt (B * C)) ^ 2 = B * C := Real.sq_sqrt hBC_nonneg
    have hsqrt_nonneg : 0 ≤ Real.sqrt (B * C) := Real.sqrt_nonneg _
    nlinarith
  have hxy_nonneg : 0 ≤ x * y := mul_nonneg hx hy
  have hmul : (2 : ℝ) * A * x * y ≤ (2 : ℝ) * Real.sqrt (B * C) * x * y := by
    nlinarith
  have hsqrt_mul : Real.sqrt (B * C) = Real.sqrt B * Real.sqrt C := by
    rw [Real.sqrt_mul]
    exact hB
  have htwo :
      (2 : ℝ) * (Real.sqrt C * x) * (Real.sqrt B * y) ≤
        (Real.sqrt C * x) ^ 2 + (Real.sqrt B * y) ^ 2 :=
    concrete_l2_two_mul_le_sq_add_sq (Real.sqrt C * x) (Real.sqrt B * y)
  have hrewrite_left :
      (2 : ℝ) * Real.sqrt (B * C) * x * y =
        (2 : ℝ) * (Real.sqrt C * x) * (Real.sqrt B * y) := by
    rw [hsqrt_mul]
    ring
  have hrewrite_right :
      (Real.sqrt C * x) ^ 2 + (Real.sqrt B * y) ^ 2 =
        B * y ^ 2 + C * x ^ 2 := by
    have hCsq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
    have hBsq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
    rw [mul_pow, mul_pow, hCsq, hBsq]
    ring
  exact hmul.trans ((le_of_eq hrewrite_left).trans (htwo.trans_eq hrewrite_right))

/-- Package: scalar mixed-term estimate for finite Cauchy. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixed : Prop :=
  ∀ A B C x y : ℝ,
    0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ x → 0 ≤ y → A ^ 2 ≤ B * C →
      (2 : ℝ) * A * x * y ≤ B * y ^ 2 + C * x ^ 2

/-- The scalar mixed-term package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_mixed :
    concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixed := by
  intro A B C x y hA hB hC hx hy hbase
  exact concrete_l2_finite_cauchy_scalar_mixed hA hB hC hx hy hbase

/--
Full scalar induction step for finite Cauchy.
-/
theorem concrete_l2_finite_cauchy_scalar_step
    {A B C x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hbase : A ^ 2 ≤ B * C) :
    (A + x * y) ^ 2 ≤ (B + x ^ 2) * (C + y ^ 2) := by
  exact concrete_l2_finite_cauchy_scalar_step_from_mixed hbase
    (concrete_l2_finite_cauchy_scalar_mixed hA hB hC hx hy hbase)

/-- Package: full scalar induction step for finite Cauchy. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStep : Prop :=
  ∀ A B C x y : ℝ,
    0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ x → 0 ≤ y → A ^ 2 ≤ B * C →
      (A + x * y) ^ 2 ≤ (B + x ^ 2) * (C + y ^ 2)

/-- The full scalar induction step package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step :
    concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStep := by
  intro A B C x y hA hB hC hx hy hbase
  exact concrete_l2_finite_cauchy_scalar_step hA hB hC hx hy hbase

/-- Surface for the scalar mixed and full scalar induction step. -/
structure ConcreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixedSurface where
  stepFromMixedReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurfaceReady
  mixed : concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixed
  scalarStep : concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStep
  boundaryNotFinitePrefixSquareCauchy : Prop
  boundaryNotSummedCauchy : Prop

/-- Concrete scalar mixed surface. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixedSurface :
    ConcreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixedSurface :=
  { stepFromMixedReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step_from_mixed_surface_ready
    mixed := concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_mixed
    scalarStep := concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step
    boundaryNotFinitePrefixSquareCauchy := True
    boundaryNotSummedCauchy := True }

/-- Readiness predicate for scalar mixed surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarMixedSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarStepFromMixedSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FiniteCauchyScalarMixed ∧
  concreteL2MathlibSpectralAuditR2FiniteCauchyScalarStep

/-- Readiness theorem for scalar mixed surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_mixed_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyScalarMixedSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step_from_mixed_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_mixed,
    concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_scalar_step⟩

end

end MathlibAnalytic
end MGAP4D
