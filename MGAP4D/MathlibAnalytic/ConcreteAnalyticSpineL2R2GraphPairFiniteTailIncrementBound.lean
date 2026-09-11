import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairUniformFiniteTailBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- A finite block-energy upper bound is exactly a finite partial-energy
increment upper bound. -/
theorem concrete_l2_graph_pair_partial_energy_increment_le_of_block_energy_le
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) {ε : ℝ}
    (hε : concreteL2GraphPairBlockEnergy p M K ≤ ε) :
    concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ ε := by
  rw [concrete_l2_graph_pair_partial_energy_sub_eq_block_energy]
  exact hε

/-- A finite block-energy upper bound yields a two-sided finite increment packet:
nonnegativity plus the requested upper bound. -/
theorem concrete_l2_graph_pair_partial_energy_increment_nonneg_and_le_of_block_energy_le
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) {ε : ℝ}
    (hε : concreteL2GraphPairBlockEnergy p M K ≤ ε) :
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ∧
    concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ ε :=
  ⟨concrete_l2_graph_pair_partial_energy_increment_nonneg p M K,
    concrete_l2_graph_pair_partial_energy_increment_le_of_block_energy_le p M K hε⟩

/-- A uniform finite partial-energy bound gives a finite increment bound for every
finite block. -/
theorem concrete_l2_graph_pair_partial_energy_increment_le_of_uniform_partial_energy_le
    (p : ConcreteL2GraphPairSpace) {C : ℝ}
    (hC : ∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C)
    (M K : ℕ) :
    concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ C :=
  concrete_l2_graph_pair_partial_energy_increment_le_of_block_energy_le p M K
    (concrete_l2_graph_pair_uniform_finite_tail_bound p hC M K)

/-- A tail-start partial-energy bound gives a finite increment bound for every
finite block whose start lies in the tail. -/
theorem concrete_l2_graph_pair_partial_energy_increment_le_of_tail_partial_energy_le
    (p : ConcreteL2GraphPairSpace) (N M K : ℕ) {C : ℝ}
    (hNM : N ≤ M)
    (hC : ∀ L : ℕ, N ≤ L → concreteL2GraphPairPartialEnergy p L ≤ C) :
    concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ C :=
  concrete_l2_graph_pair_partial_energy_increment_le_of_block_energy_le p M K
    (concrete_l2_graph_pair_uniform_tail_start_finite_bound p N hC M K hNM)

/-- Adapter predicate for finite-tail increment bounds. -/
def concreteL2R2GraphPairFiniteTailIncrementBoundAdapter : Prop :=
  ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ) {ε : ℝ},
    concreteL2GraphPairBlockEnergy p M K ≤ ε →
    concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ ε

/-- Adapter theorem for finite-tail increment bounds. -/
theorem concrete_l2_r2_graph_pair_finite_tail_increment_bound_adapter_ready :
    concreteL2R2GraphPairFiniteTailIncrementBoundAdapter := by
  intro p M K ε hε
  exact concrete_l2_graph_pair_partial_energy_increment_le_of_block_energy_le p M K hε

/-- R2t finite-tail increment-bound surface.

This is the finite ε-estimate surface just before any genuine tail convergence or
Cauchy criterion.  It turns finite block-energy bounds into finite partial-energy
increment bounds while preserving the boundary: no infinite graph norm, no Cauchy
criterion, no graph-norm density, no closed-operator theorem, no self-adjointness,
and no spectral theorem/PVM/positive-weight claim. -/
structure ConcreteL2R2GraphPairFiniteTailIncrementBoundSurface where
  uniformFiniteTailBoundReady : concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundSurfaceReady
  incrementBoundFromBlockBound :
    ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ) {ε : ℝ},
      concreteL2GraphPairBlockEnergy p M K ≤ ε →
      concreteL2GraphPairPartialEnergy p (M + K) -
          concreteL2GraphPairPartialEnergy p M ≤ ε
  incrementNonnegAndBoundFromBlockBound :
    ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ) {ε : ℝ},
      concreteL2GraphPairBlockEnergy p M K ≤ ε →
      0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
          concreteL2GraphPairPartialEnergy p M ∧
      concreteL2GraphPairPartialEnergy p (M + K) -
          concreteL2GraphPairPartialEnergy p M ≤ ε
  uniformPartialBoundGivesIncrementBound :
    ∀ (p : ConcreteL2GraphPairSpace) {C : ℝ},
      (∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C) →
      ∀ M K : ℕ,
        concreteL2GraphPairPartialEnergy p (M + K) -
          concreteL2GraphPairPartialEnergy p M ≤ C
  tailPartialBoundGivesIncrementBound :
    ∀ (p : ConcreteL2GraphPairSpace) (N M K : ℕ) {C : ℝ},
      N ≤ M →
      (∀ L : ℕ, N ≤ L → concreteL2GraphPairPartialEnergy p L ≤ C) →
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ C
  boundaryNotTailLimit : Prop
  boundaryNotTailConvergence : Prop
  boundaryNotCauchyCriterion : Prop
  boundaryNotInfiniteGraphNorm : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2t finite-tail increment-bound surface. -/
def concreteL2R2GraphPairFiniteTailIncrementBoundSurface :
    ConcreteL2R2GraphPairFiniteTailIncrementBoundSurface :=
  { uniformFiniteTailBoundReady :=
      concrete_analytic_spine_l2_r2_graph_pair_uniform_finite_tail_bound_surface_ready
    incrementBoundFromBlockBound := by
      intro p M K ε hε
      exact concrete_l2_graph_pair_partial_energy_increment_le_of_block_energy_le p M K hε
    incrementNonnegAndBoundFromBlockBound := by
      intro p M K ε hε
      exact concrete_l2_graph_pair_partial_energy_increment_nonneg_and_le_of_block_energy_le p M K hε
    uniformPartialBoundGivesIncrementBound := by
      intro p C hC M K
      exact concrete_l2_graph_pair_partial_energy_increment_le_of_uniform_partial_energy_le p hC M K
    tailPartialBoundGivesIncrementBound := by
      intro p N M K C hNM hC
      exact concrete_l2_graph_pair_partial_energy_increment_le_of_tail_partial_energy_le p N M K hNM hC
    boundaryNotTailLimit := True
    boundaryNotTailConvergence := True
    boundaryNotCauchyCriterion := True
    boundaryNotInfiniteGraphNorm := True
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2t readiness. -/
def concreteAnalyticSpineL2R2GraphPairFiniteTailIncrementBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundSurfaceReady ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundAdapter ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotTailLimit ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotTailConvergence ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotCauchyCriterion ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairFiniteTailIncrementBoundSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2t. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_finite_tail_increment_bound_surface_ready :
    concreteAnalyticSpineL2R2GraphPairFiniteTailIncrementBoundSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairFiniteTailIncrementBoundSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_uniform_finite_tail_bound_surface_ready <|
      And.intro concrete_l2_r2_graph_pair_finite_tail_increment_bound_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2t. -/
def concreteAnalyticSpineL2R2GraphPairFiniteTailIncrementBoundHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairFiniteTailIncrementBoundSurfaceReady

/-- Boundary theorem for R2t. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_finite_tail_increment_bound_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairFiniteTailIncrementBoundHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_finite_tail_increment_bound_surface_ready

end

end MathlibAnalytic
end MGAP4D
