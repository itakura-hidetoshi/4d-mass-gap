import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSquare

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
General finite sqrt-form Cauchy inequality for nonnegative real vectors over a
`Finset ℕ`.

This is derived from the square-form Cauchy theorem already proved in this PR.
No fragile external Cauchy--Schwarz theorem name is used.
-/
theorem concrete_l2_finite_cauchy_general_sqrt
    (s : Finset ℕ) (x y : ℕ → ℝ)
    (hx : ∀ n : ℕ, 0 ≤ x n) (hy : ∀ n : ℕ, 0 ≤ y n) :
    Finset.sum s (fun n : ℕ => x n * y n) ≤
      Real.sqrt (Finset.sum s (fun n : ℕ => x n ^ 2)) *
        Real.sqrt (Finset.sum s (fun n : ℕ => y n ^ 2)) := by
  let D := Finset.sum s (fun n : ℕ => x n * y n)
  let B := Finset.sum s (fun n : ℕ => x n ^ 2)
  let C := Finset.sum s (fun n : ℕ => y n ^ 2)
  have hD : 0 ≤ D := by
    dsimp [D]
    refine Finset.sum_nonneg ?_
    intro n hn
    exact mul_nonneg (hx n) (hy n)
  have hB : 0 ≤ B := by
    dsimp [B]
    refine Finset.sum_nonneg ?_
    intro n hn
    exact sq_nonneg (x n)
  have hC : 0 ≤ C := by
    dsimp [C]
    refine Finset.sum_nonneg ?_
    intro n hn
    exact sq_nonneg (y n)
  have hsq : D ^ 2 ≤ B * C := by
    dsimp [D, B, C]
    exact concrete_l2_finite_cauchy_general_square s x y hx hy
  have hR_nonneg : 0 ≤ Real.sqrt B * Real.sqrt C :=
    mul_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg C)
  have hR_sq : (Real.sqrt B * Real.sqrt C) ^ 2 = B * C := by
    rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hC]
  have hle : D ≤ Real.sqrt B * Real.sqrt C := by
    nlinarith
  exact hle

/-- Package: general finite sqrt-form Cauchy. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrt : Prop :=
  ∀ (s : Finset ℕ) (x y : ℕ → ℝ),
    (∀ n : ℕ, 0 ≤ x n) → (∀ n : ℕ, 0 ≤ y n) →
      Finset.sum s (fun n : ℕ => x n * y n) ≤
        Real.sqrt (Finset.sum s (fun n : ℕ => x n ^ 2)) *
          Real.sqrt (Finset.sum s (fun n : ℕ => y n ^ 2))

/-- The general finite sqrt-form Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_general_sqrt :
    concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrt := by
  intro s x y hx hy
  exact concrete_l2_finite_cauchy_general_sqrt s x y hx hy

/-- Surface for the general finite sqrt-form Cauchy theorem. -/
structure ConcreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurface where
  squareReady : concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurfaceReady
  sqrtCauchy : concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrt
  boundaryNotSpecializedFiniteCauchy : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete surface for the general finite sqrt-form Cauchy theorem. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurface :
    ConcreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurface :=
  { squareReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_square_surface_ready
    sqrtCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_general_sqrt
    boundaryNotSpecializedFiniteCauchy := True
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the general finite sqrt-form Cauchy surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrt

/-- Readiness theorem for the general finite sqrt-form Cauchy surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_sqrt_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_square_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_general_sqrt⟩

end

end MathlibAnalytic
end MGAP4D
