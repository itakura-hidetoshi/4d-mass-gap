import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSummedCauchyFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Finite-prefix Cauchy frontier.

This is the next genuinely mathematical step after pointwise Cauchy.  The full
finite-prefix Cauchy theorem is not asserted yet; instead this file exposes the
finite nonnegative vectors that will be fed into a finite-dimensional
Cauchy--Schwarz proof.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchyFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSummedCauchyFrontierSurfaceReady

/-- Readiness theorem for the finite-prefix Cauchy frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_frontier_ready :
    concreteL2MathlibSpectralAuditR2FinitePrefixCauchyFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_summed_cauchy_frontier_surface_ready

/-- Left finite vector of square-root energies. -/
def concreteL2FinitePrefixSqrtEnergyLeft
    (p : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∈ s then Real.sqrt (concreteL2GraphPairEnergyTerm p n) else 0

/-- Right finite vector of square-root energies. -/
def concreteL2FinitePrefixSqrtEnergyRight
    (q : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∈ s then Real.sqrt (concreteL2GraphPairEnergyTerm q n) else 0

/-- Nonnegativity of the left finite-prefix square-root energy vector. -/
theorem concrete_l2_finite_prefix_sqrt_energy_left_nonneg
    (p : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ) :
    0 ≤ concreteL2FinitePrefixSqrtEnergyLeft p s n := by
  unfold concreteL2FinitePrefixSqrtEnergyLeft
  by_cases hn : n ∈ s
  · simp [hn, Real.sqrt_nonneg]
  · simp [hn]

/-- Nonnegativity of the right finite-prefix square-root energy vector. -/
theorem concrete_l2_finite_prefix_sqrt_energy_right_nonneg
    (q : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ) :
    0 ≤ concreteL2FinitePrefixSqrtEnergyRight q s n := by
  unfold concreteL2FinitePrefixSqrtEnergyRight
  by_cases hn : n ∈ s
  · simp [hn, Real.sqrt_nonneg]
  · simp [hn]

/--
On the prefix, the product of the finite-prefix vectors is the product of the
energy square roots.
-/
theorem concrete_l2_finite_prefix_sqrt_energy_mul_on_prefix
    (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ) {n : ℕ} (hn : n ∈ s) :
    concreteL2FinitePrefixSqrtEnergyLeft p s n *
        concreteL2FinitePrefixSqrtEnergyRight q s n =
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) := by
  simp [concreteL2FinitePrefixSqrtEnergyLeft, concreteL2FinitePrefixSqrtEnergyRight, hn]

/--
On the prefix, the square of the left finite-prefix vector is the energy term.
-/
theorem concrete_l2_finite_prefix_sqrt_energy_left_sq_on_prefix
    (p : ConcreteL2GraphPairSpace) (s : Finset ℕ) {n : ℕ} (hn : n ∈ s) :
    concreteL2FinitePrefixSqrtEnergyLeft p s n ^ 2 =
      concreteL2GraphPairEnergyTerm p n := by
  have hnonneg : 0 ≤ concreteL2GraphPairEnergyTerm p n :=
    concrete_l2_graph_pair_energy_term_nonneg p n
  simp [concreteL2FinitePrefixSqrtEnergyLeft, hn, Real.sq_sqrt hnonneg]

/--
On the prefix, the square of the right finite-prefix vector is the energy term.
-/
theorem concrete_l2_finite_prefix_sqrt_energy_right_sq_on_prefix
    (q : ConcreteL2GraphPairSpace) (s : Finset ℕ) {n : ℕ} (hn : n ∈ s) :
    concreteL2FinitePrefixSqrtEnergyRight q s n ^ 2 =
      concreteL2GraphPairEnergyTerm q n := by
  have hnonneg : 0 ≤ concreteL2GraphPairEnergyTerm q n :=
    concrete_l2_graph_pair_energy_term_nonneg q n
  simp [concreteL2FinitePrefixSqrtEnergyRight, hn, Real.sq_sqrt hnonneg]

/--
Finite-prefix Cauchy proof obligation, now expressed through explicit finite
vectors.  This is the exact finite-dimensional lemma to prove next.
-/
def concreteL2MathlibSpectralAuditR2FinitePrefixVectorCauchyTarget : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (s : Finset ℕ),
    Finset.sum s
        (fun n : ℕ =>
          concreteL2FinitePrefixSqrtEnergyLeft p s n *
            concreteL2FinitePrefixSqrtEnergyRight q s n) ≤
      Real.sqrt
          (Finset.sum s
            (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyLeft p s n ^ 2)) *
        Real.sqrt
          (Finset.sum s
            (fun n : ℕ => concreteL2FinitePrefixSqrtEnergyRight q s n ^ 2))

/-- Finite-prefix Cauchy frontier surface. -/
structure ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurface where
  summedCauchyFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSummedCauchyFrontierSurfaceReady
  leftNonneg : ∀ (p : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ),
    0 ≤ concreteL2FinitePrefixSqrtEnergyLeft p s n
  rightNonneg : ∀ (q : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ),
    0 ≤ concreteL2FinitePrefixSqrtEnergyRight q s n
  vectorCauchyTarget : Prop
  boundaryNotFinitePrefixCauchy : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete finite-prefix Cauchy frontier surface. -/
def concreteL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurface :=
  { summedCauchyFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_summed_cauchy_frontier_surface_ready
    leftNonneg := concrete_l2_finite_prefix_sqrt_energy_left_nonneg
    rightNonneg := concrete_l2_finite_prefix_sqrt_energy_right_nonneg
    vectorCauchyTarget :=
      concreteL2MathlibSpectralAuditR2FinitePrefixVectorCauchyTarget
    boundaryNotFinitePrefixCauchy := True
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the finite-prefix Cauchy frontier surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2FinitePrefixCauchyFrontier ∧
  (∀ (p : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ),
    0 ≤ concreteL2FinitePrefixSqrtEnergyLeft p s n) ∧
  (∀ (q : ConcreteL2GraphPairSpace) (s : Finset ℕ) (n : ℕ),
    0 ≤ concreteL2FinitePrefixSqrtEnergyRight q s n)

/-- Readiness theorem for the finite-prefix Cauchy frontier surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyFrontierSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_frontier_ready,
    concrete_l2_finite_prefix_sqrt_energy_left_nonneg,
    concrete_l2_finite_prefix_sqrt_energy_right_nonneg⟩

end

end MathlibAnalytic
end MGAP4D
