import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Uniform finite-prefix Cauchy package.

This is the same specialized finite-prefix Cauchy theorem, repackaged as a
uniform estimate over all finite subsets.  It is the right input for the later
passage from finite sums to `tsum`.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchyUniform : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace),
    ∀ s : Finset ℕ,
      Finset.sum s
          (fun n : ℕ =>
            Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
              Real.sqrt (concreteL2GraphPairEnergyTerm q n)) ≤
        Real.sqrt (Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm p n)) *
          Real.sqrt (Finset.sum s (fun n : ℕ => concreteL2GraphPairEnergyTerm q n))

/-- The uniform finite-prefix Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_sqrt_energy_cauchy_uniform :
    concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchyUniform := by
  intro p q s
  exact concrete_l2_finite_prefix_sqrt_energy_cauchy p q s

/--
Finite-prefix Cauchy uniform surface.
-/
structure ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurface where
  finitePrefixReady : concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySurfaceReady
  uniformFinitePrefixCauchy : concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchyUniform
  boundaryNotTsumCauchy : Prop
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete finite-prefix Cauchy uniform surface. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurface :
    ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurface :=
  { finitePrefixReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_surface_ready
    uniformFinitePrefixCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_finite_prefix_sqrt_energy_cauchy_uniform
    boundaryNotTsumCauchy := True
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the uniform finite-prefix Cauchy surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2FinitePrefixSqrtEnergyCauchyUniform

/-- Readiness theorem for the uniform finite-prefix Cauchy surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_uniform_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_prefix_sqrt_energy_cauchy_uniform⟩

end

end MathlibAnalytic
end MGAP4D
