import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCrossTermExpansion

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Pointwise Cauchy--Schwarz for the concrete graph-pair cross term.

At each coordinate, a graph pair gives a vector in `ℝ²`; this lemma is exactly
Cauchy--Schwarz for that `ℝ²` vector, written in the concrete coordinate form
used by the graph-pair energy.
-/
theorem concrete_l2_graph_pair_cross_term_pointwise_cauchy
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairCrossTerm p q n ≤
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
  have hcs_sq : (x₁ * y₁ + x₂ * y₂) ^ 2 ≤ (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁)]
  have hprod_nonneg : 0 ≤ (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) :=
    mul_nonneg hx_nonneg hy_nonneg
  have hsqrt_prod_sq :
      (Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2))) ^ 2 =
        (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
    exact Real.sq_sqrt hprod_nonneg
  have hdot_le_sqrt_prod :
      x₁ * y₁ + x₂ * y₂ ≤
        Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) := by
    have hright_nonneg : 0 ≤ Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) :=
      Real.sqrt_nonneg _
    nlinarith
  have hsqrt_mul :
      Real.sqrt ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) =
        Real.sqrt (x₁ ^ 2 + x₂ ^ 2) * Real.sqrt (y₁ ^ 2 + y₂ ^ 2) := by
    rw [Real.sqrt_mul]
    · exact hx_nonneg
  unfold concreteL2GraphPairCrossTerm concreteL2GraphPairEnergyTerm
  dsimp [x₁, x₂, y₁, y₂] at hdot_le_sqrt_prod hsqrt_mul
  exact hdot_le_sqrt_prod.trans_eq hsqrt_mul

/-- Pointwise Cauchy package for the concrete graph-pair cross term. -/
def concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchy : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairCrossTerm p q n ≤
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)

/-- The pointwise Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_pointwise_cauchy :
    concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchy := by
  exact concrete_l2_graph_pair_cross_term_pointwise_cauchy

/--
Pointwise Cauchy surface for the graph-pair cross term.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormPointwiseCauchySurface where
  crossTermExpansionReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurfaceReady
  pointwiseCauchy : concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchy
  boundaryNotSummedCauchy : Prop
  boundaryNotMinkowskiSquare : Prop
  boundaryNotExactTriangle : Prop
  boundaryNotTopology : Prop

/-- Concrete pointwise Cauchy surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormPointwiseCauchySurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormPointwiseCauchySurface :=
  { crossTermExpansionReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_cross_term_expansion_surface_ready
    pointwiseCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_pointwise_cauchy
    boundaryNotSummedCauchy := True
    boundaryNotMinkowskiSquare := True
    boundaryNotExactTriangle := True
    boundaryNotTopology := True }

/-- Readiness predicate for the pointwise Cauchy surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPointwiseCauchySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchy

/-- Readiness theorem for the pointwise Cauchy surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_pointwise_cauchy_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPointwiseCauchySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_cross_term_expansion_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_cross_term_pointwise_cauchy⟩

end

end MathlibAnalytic
end MGAP4D
