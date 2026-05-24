import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Absolute pointwise Cauchy--Schwarz for the concrete graph-pair cross term.

This is the correct bridge toward cross-term summability, since the cross term
itself can have either sign.  The proof follows the already-CI-passing
pointwise Cauchy proof, but keeps the squared estimate and converts it to an
absolute-value estimate before rewriting the square-root product.
-/
theorem concrete_l2_graph_pair_cross_term_abs_pointwise_cauchy
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    |concreteL2GraphPairCrossTerm p q n| ≤
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) := by
  let x₁ := (concreteL2GraphPairFst p).1 n
  let x₂ := (concreteL2GraphPairSnd p).1 n
  let y₁ := (concreteL2GraphPairFst q).1 n
  let y₂ := (concreteL2GraphPairSnd q).1 n
  have hx_nonneg : 0 ≤ x₁ ^ 2 + x₂ ^ 2 := by
    nlinarith [sq_nonneg x₁, sq_nonneg x₂]
  have hy_nonneg : 0 ≤ y₁ ^ 2 + y₂ ^ 2 := by
    nlinarith [sq_nonneg y₁, sq_nonneg y₂]
  have hprod_nonneg : 0 ≤ (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) :=
    mul_nonneg hx_nonneg hy_nonneg
  have hcs_sq :
      (x₁ * y₁ + x₂ * y₂) ^ 2 ≤
        (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁)]
  have hsqrt_prod_sq :
      (Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2))) ^ 2 =
        (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
    exact Real.sq_sqrt hprod_nonneg
  have h_abs_le_sqrt :
      |x₁ * y₁ + x₂ * y₂| ≤
        Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) := by
    have hright_nonneg :
        0 ≤ Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) :=
      Real.sqrt_nonneg _
    have h_abs_sq :
        |x₁ * y₁ + x₂ * y₂| ^ 2 ≤
          (Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2))) ^ 2 := by
      rw [sq_abs]
      simpa [hsqrt_prod_sq] using hcs_sq
    nlinarith [abs_nonneg (x₁ * y₁ + x₂ * y₂), hright_nonneg, h_abs_sq]
  have hsqrt_mul :
      Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) =
        Real.sqrt (x₁ ^ 2 + x₂ ^ 2) * Real.sqrt (y₁ ^ 2 + y₂ ^ 2) := by
    rw [Real.sqrt_mul]
    · exact hx_nonneg
  unfold concreteL2GraphPairCrossTerm concreteL2GraphPairEnergyTerm
  dsimp [x₁, x₂, y₁, y₂] at h_abs_le_sqrt hsqrt_mul
  exact h_abs_le_sqrt.trans_eq hsqrt_mul

/-- Package: absolute pointwise Cauchy for the graph-pair cross term. -/
def concreteL2MathlibSpectralAuditR2GraphPairCrossTermAbsPointwiseCauchy : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    |concreteL2GraphPairCrossTerm p q n| ≤
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)

/-- The absolute pointwise Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_abs_pointwise_cauchy :
    concreteL2MathlibSpectralAuditR2GraphPairCrossTermAbsPointwiseCauchy := by
  intro p q n
  exact concrete_l2_graph_pair_cross_term_abs_pointwise_cauchy p q n

/-- Surface for absolute pointwise Cauchy of the graph-pair cross term. -/
structure ConcreteL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurface where
  crossTermFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurfaceReady
  absPointwiseCauchy : concreteL2MathlibSpectralAuditR2GraphPairCrossTermAbsPointwiseCauchy
  boundaryNotCrossTermSummability : Prop
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete surface for absolute pointwise Cauchy of the cross term. -/
def concreteL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurface :=
  { crossTermFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_frontier_surface_ready
    absPointwiseCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_abs_pointwise_cauchy
    boundaryNotCrossTermSummability := True
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for absolute pointwise Cauchy of the cross term. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchyFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphPairCrossTermAbsPointwiseCauchy

/-- Readiness theorem for absolute pointwise Cauchy of the cross term. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_abs_pointwise_cauchy_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_abs_pointwise_cauchy⟩

end

end MathlibAnalytic
end MGAP4D
