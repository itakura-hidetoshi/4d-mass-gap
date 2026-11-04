import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairFiniteTailBounds

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- A finite partial-energy bound above a start index controls all finite blocks
whose end lies under the same bound. -/
theorem concrete_l2_graph_pair_block_energy_le_of_endpoint_partial_energy_le
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) {C : ℝ}
    (hC : concreteL2GraphPairPartialEnergy p (M + K) ≤ C) :
    concreteL2GraphPairBlockEnergy p M K ≤ C :=
  concrete_l2_graph_pair_block_energy_le_of_later_partial_energy_le p M K hC

/-- A tail-indexed partial-energy upper bound controls every finite block starting
at or beyond the tail index, provided the block endpoint also lies in the tail. -/
theorem concrete_l2_graph_pair_block_energy_le_of_tail_partial_energy_le
    (p : ConcreteL2GraphPairSpace) (N M K : ℕ) {C : ℝ}
    (hNM : N ≤ M)
    (hC : ∀ L : ℕ, N ≤ L → concreteL2GraphPairPartialEnergy p L ≤ C) :
    concreteL2GraphPairBlockEnergy p M K ≤ C := by
  exact concrete_l2_graph_pair_block_energy_le_of_endpoint_partial_energy_le p M K
    (hC (M + K) (le_trans hNM (Nat.le_add_right M K)))

/-- Uniform finite-tail bound stated over all starts and widths. -/
theorem concrete_l2_graph_pair_uniform_finite_tail_bound
    (p : ConcreteL2GraphPairSpace) {C : ℝ}
    (hC : ∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C) :
    ∀ M K : ℕ, concreteL2GraphPairBlockEnergy p M K ≤ C :=
  concrete_l2_graph_pair_block_energy_le_of_uniform_partial_energy_le p hC

/-- Uniform finite-tail bound with explicit tail start. -/
theorem concrete_l2_graph_pair_uniform_tail_start_finite_bound
    (p : ConcreteL2GraphPairSpace) (N : ℕ) {C : ℝ}
    (hC : ∀ L : ℕ, N ≤ L → concreteL2GraphPairPartialEnergy p L ≤ C) :
    ∀ M K : ℕ, N ≤ M → concreteL2GraphPairBlockEnergy p M K ≤ C := by
  intro M K hNM
  exact concrete_l2_graph_pair_block_energy_le_of_tail_partial_energy_le p N M K hNM hC

/-- Adapter predicate for uniform finite-tail bounds. -/
def concreteL2R2GraphPairUniformFiniteTailBoundAdapter : Prop :=
  ∀ (p : ConcreteL2GraphPairSpace) {C : ℝ},
    (∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C) →
    ∀ M K : ℕ, concreteL2GraphPairBlockEnergy p M K ≤ C

/-- Adapter theorem for uniform finite-tail bounds. -/
theorem concrete_l2_r2_graph_pair_uniform_finite_tail_bound_adapter_ready :
    concreteL2R2GraphPairUniformFiniteTailBoundAdapter := by
  intro p C hC M K
  exact concrete_l2_graph_pair_uniform_finite_tail_bound p hC M K

/-- R2s uniform finite-tail bound surface.

This is the finite estimate façade that turns a uniform partial-energy bound into
uniform finite block-energy bounds.  It is deliberately still finite: it does not
assert convergence of tails, a Cauchy criterion, an infinite graph norm,
graph-norm density, closed-operator facts, self-adjointness, or spectral theory. -/
structure ConcreteL2R2GraphPairUniformFiniteTailBoundSurface where
  finiteTailBoundsReady : concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsSurfaceReady
  uniformFiniteTailBound :
    ∀ (p : ConcreteL2GraphPairSpace) {C : ℝ},
      (∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C) →
      ∀ M K : ℕ, concreteL2GraphPairBlockEnergy p M K ≤ C
  uniformTailStartFiniteBound :
    ∀ (p : ConcreteL2GraphPairSpace) (N : ℕ) {C : ℝ},
      (∀ L : ℕ, N ≤ L → concreteL2GraphPairPartialEnergy p L ≤ C) →
      ∀ M K : ℕ, N ≤ M → concreteL2GraphPairBlockEnergy p M K ≤ C
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

/-- Concrete R2s uniform finite-tail bound surface. -/
def concreteL2R2GraphPairUniformFiniteTailBoundSurface :
    ConcreteL2R2GraphPairUniformFiniteTailBoundSurface :=
  { finiteTailBoundsReady :=
      concrete_analytic_spine_l2_r2_graph_pair_finite_tail_bounds_surface_ready
    uniformFiniteTailBound := by
      intro p C hC M K
      exact concrete_l2_graph_pair_uniform_finite_tail_bound p hC M K
    uniformTailStartFiniteBound := by
      intro p N C hC M K hNM
      exact concrete_l2_graph_pair_uniform_tail_start_finite_bound p N hC M K hNM
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

/-- R2s readiness. -/
def concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsSurfaceReady ∧
  concreteL2R2GraphPairUniformFiniteTailBoundAdapter ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotTailLimit ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotTailConvergence ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotCauchyCriterion ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairUniformFiniteTailBoundSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2s. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_uniform_finite_tail_bound_surface_ready :
    concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_finite_tail_bounds_surface_ready <|
      And.intro concrete_l2_r2_graph_pair_uniform_finite_tail_bound_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2s. -/
def concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundSurfaceReady

/-- Boundary theorem for R2s. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_uniform_finite_tail_bound_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairUniformFiniteTailBoundHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_uniform_finite_tail_bound_surface_ready

end

end MathlibAnalytic
end MGAP4D
