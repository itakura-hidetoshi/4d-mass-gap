import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
General finite square-form Cauchy inequality for nonnegative real vectors over a
`Finset ℕ`.

This avoids relying on a fragile theorem-name search for Cauchy--Schwarz in
mathlib.  The proof uses only `Finset.induction_on`, `Finset.sum_insert`,
`Finset.sum_nonneg`, and the scalar induction step already proved in this PR.
-/
theorem concrete_l2_finite_cauchy_general_square
    (s : Finset ℕ) (x y : ℕ → ℝ)
    (hx : ∀ n : ℕ, 0 ≤ x n) (hy : ∀ n : ℕ, 0 ≤ y n) :
    (Finset.sum s (fun n : ℕ => x n * y n)) ^ 2 ≤
      (Finset.sum s (fun n : ℕ => x n ^ 2)) *
        (Finset.sum s (fun n : ℕ => y n ^ 2)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hA : 0 ≤ Finset.sum s (fun n : ℕ => x n * y n) := by
      refine Finset.sum_nonneg ?_
      intro n hn
      exact mul_nonneg (hx n) (hy n)
    have hB : 0 ≤ Finset.sum s (fun n : ℕ => x n ^ 2) := by
      refine Finset.sum_nonneg ?_
      intro n hn
      exact sq_nonneg (x n)
    have hC : 0 ≤ Finset.sum s (fun n : ℕ => y n ^ 2) := by
      refine Finset.sum_nonneg ?_
      intro n hn
      exact sq_nonneg (y n)
    have hstep :=
      concrete_l2_finite_cauchy_scalar_step
        hA hB hC (hx a) (hy a) ih
    simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hstep

/-- Package: general finite square-form Cauchy. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquare : Prop :=
  ∀ (s : Finset ℕ) (x y : ℕ → ℝ),
    (∀ n : ℕ, 0 ≤ x n) → (∀ n : ℕ, 0 ≤ y n) →
      (Finset.sum s (fun n : ℕ => x n * y n)) ^ 2 ≤
        (Finset.sum s (fun n : ℕ => x n ^ 2)) *
          (Finset.sum s (fun n : ℕ => y n ^ 2))

/-- The general finite square-form Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_general_square :
    concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquare := by
  intro s x y hx hy
  exact concrete_l2_finite_cauchy_general_square s x y hx hy

/-- Surface for the general finite square-form Cauchy theorem. -/
structure ConcreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurface where
  generalFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralFrontierSurfaceReady
  squareCauchy : concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquare
  boundaryNotGeneralSqrtCauchy : Prop
  boundaryNotSpecializedFiniteCauchy : Prop
  boundaryNotSummedCauchy : Prop

/-- Concrete surface for the general finite square-form Cauchy theorem. -/
def concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurface :
    ConcreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurface :=
  { generalFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_frontier_surface_ready
    squareCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_general_square
    boundaryNotGeneralSqrtCauchy := True
    boundaryNotSpecializedFiniteCauchy := True
    boundaryNotSummedCauchy := True }

/-- Readiness predicate for the general finite square-form Cauchy surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FiniteCauchyGeneralSquare

/-- Readiness theorem for the general finite square-form Cauchy surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_square_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSquareSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_cauchy_general_square⟩

end

end MathlibAnalytic
end MGAP4D
