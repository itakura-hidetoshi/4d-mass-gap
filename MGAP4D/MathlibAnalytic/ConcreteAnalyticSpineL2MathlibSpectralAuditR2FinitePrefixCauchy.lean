import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrt

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Specialized finite-prefix Cauchy inequality for the concrete square-root energy
terms.

This specializes the general finite sqrt-form Cauchy theorem to the finite
vectors prepared from `sqrt (energyTerm p n)` and `sqrt (energyTerm q n)`.
-/
theorem concrete_l2_finite_prefix_sqrt_energy_cauchy
    (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ) :
    Finset.sum s
        (fun n : ℕ =>
          Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
            Real.sqrt (concreteL2GraphPairEnergyTerm q n)) ≤
      Real.sqrt (Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm p n)) *
        Real.sqrt (Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm q n)) := by
  have hmain :=
    concrete_l2_finite_cauchy_general_sqrt s
      (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyLeft p s n)
      (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyRight q s n)
      (concrete_l2_finite_prefix_sqrt_energy_left_nonneg p s)
      (concrete_l2_finite_prefix_sqrt_energy_right_nonneg q s)
  have hprod :
      Finset.sum s
          (fun n : ℕ =>
            concreteL2FinitePrefixSqrtEnergyLeft p s n *
              concreteL2FinitePrefixSqrtEnergyRight q s n) =
        Finset.sum s
          (fun n : ℕ =>
            Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
              Real.sqrt (concreteL2GraphPairEnergyTerm q n)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact concrete_l2_finite_prefix_sqrt_energy_mul_on_prefix p q s hn
  have hleftsq :
      Finset.sum s
          (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyLeft p s n ^ 2) =
        Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact concrete_l2_finite_prefix_sqrt_energy_left_sq_on_prefix p s hn
  have hrightsq :
      Finset.sum s
          (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyRight q s n ^ 2) =
        Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm q n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact concrete_l2_finite_prefix_sqrt_energy_right_sq_on_prefix q s hn
  rw [hprod, hleftsq, hrightsq] at hmain
  exact hmain

/-- Package: specialized finite-prefix Cauchy for square-root energy terms. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchy : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ),
    Finset.sum s
        (fun n : ℕ =>
          Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
            Real.sqrt (concreteL2GraphPairEnergyTerm q n)) ≤
      Real.sqrt (Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm p n)) *
        Real.sqrt (Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm q n))

/-- The specialized finite-prefix Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_sqrt_energy_cauchy :
    concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchy := by
  intro p q s
  exact concrete_l2_finite_prefix_sqrt_energy_cauchy p q s

/-- Surface for specialized finite-prefix Cauchy. -/
structure ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchySurface where
  generalSqrtReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurfaceReady
  finitePrefixCauchy : concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchy
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete surface for specialized finite-prefix Cauchy. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchySurface :
    ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchySurface :=
  { generalSqrtReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_sqrt_surface_ready
    finitePrefixCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_finite_prefix_sqrt_energy_cauchy
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for specialized finite-prefix Cauchy. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FiniteCauchyGeneralSqrtSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchy

/-- Readiness theorem for specialized finite-prefix Cauchy. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_cauchy_general_sqrt_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_prefix_sqrt_energy_cauchy⟩

end

end MathlibAnalytic
end MGAP4D
