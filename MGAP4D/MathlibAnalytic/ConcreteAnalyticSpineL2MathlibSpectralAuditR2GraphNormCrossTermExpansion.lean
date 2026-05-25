import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormMinkowskiFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Pointwise graph-pair cross term.

For the concrete graph-pair energy
`fst^2 + snd^2`, the cross term is the coordinatewise Euclidean inner product
of the two graph pairs.
-/
def concreteL2GraphPairCrossTerm
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) : ℝ :=
  (concreteL2GraphPairFst p).1 n * (concreteL2GraphPairFst q).1 n +
    (concreteL2GraphPairSnd p).1 n * (concreteL2GraphPairSnd q).1 n

/--
Exact pointwise energy expansion for addition of graph pairs.

This is the algebraic identity needed before any Cauchy--Schwarz/Minkowski
argument can be made.
-/
theorem concrete_l2_graph_pair_energy_add_exact_expansion
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n =
      concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n +
          (2 : ℝ) * concreteL2GraphPairCrossTerm p q n := by
  unfold concreteL2GraphPairEnergyTerm concreteL2GraphPairCrossTerm concreteL2GraphPairAdd
  simp [concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealAdd]
  ring

/--
The exact pointwise expansion package for graph-pair energy.
-/
def concreteL2MathlibSpectralAuditR2GraphPairEnergyAddExactExpansion : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n =
      concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n +
          (2 : ℝ) * concreteL2GraphPairCrossTerm p q n

/-- The exact pointwise expansion package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_energy_add_exact_expansion :
    concreteL2MathlibSpectralAuditR2GraphPairEnergyAddExactExpansion := by
  exact concrete_l2_graph_pair_energy_add_exact_expansion

/--
Pointwise Cauchy target for the graph-pair cross term.

This is the next real analytic step: the cross term should be controlled by the
pointwise energies, and then by summation-level Cauchy--Schwarz.
-/
def concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchyTarget : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairCrossTerm p q n ≤
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)

/--
Cross-term expansion surface.

This upgrades the Minkowski frontier from a mere target marker to an actual
pointwise expansion with a named cross term.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurface where
  minkowskiFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormMinkowskiFrontierSurfaceReady
  crossTerm : ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace → ℕ → ℝ
  exactExpansion : concreteL2MathlibSpectralAuditR2GraphPairEnergyAddExactExpansion
  pointwiseCauchyTarget : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop
  boundaryNotTopology : Prop

/-- Concrete cross-term expansion surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurface :=
  { minkowskiFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_minkowski_frontier_surface_ready
    crossTerm := concreteL2GraphPairCrossTerm
    exactExpansion :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_energy_add_exact_expansion
    pointwiseCauchyTarget :=
      concreteL2MathlibSpectralAuditR2GraphPairCrossTermPointwiseCauchyTarget
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True
    boundaryNotTopology := True }

/-- Readiness predicate for the cross-term expansion surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormMinkowskiFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphPairEnergyAddExactExpansion

/-- Readiness theorem for the cross-term expansion surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_cross_term_expansion_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCrossTermExpansionSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_minkowski_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_energy_add_exact_expansion⟩

end

end MathlibAnalytic
end MGAP4D
