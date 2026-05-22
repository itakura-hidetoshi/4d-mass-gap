import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairFiniteTailTelescoping

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- The finite block energy is exactly the finite partial-energy increment. -/
theorem concrete_l2_graph_pair_block_energy_eq_partial_energy_sub
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairBlockEnergy p M K =
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M := by
  rw [concrete_l2_graph_pair_partial_energy_add_block_energy]
  abel

/-- The finite partial-energy increment is exactly the finite block energy. -/
theorem concrete_l2_graph_pair_partial_energy_sub_eq_block_energy
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M =
      concreteL2GraphPairBlockEnergy p M K := by
  rw [concrete_l2_graph_pair_partial_energy_add_block_energy]
  abel

/-- The finite block energy is bounded above by the later partial energy. -/
theorem concrete_l2_graph_pair_block_energy_le_later_partial_energy
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairBlockEnergy p M K ≤
      concreteL2GraphPairPartialEnergy p (M + K) := by
  rw [concrete_l2_graph_pair_partial_energy_add_block_energy]
  have hnonneg : 0 ≤ concreteL2GraphPairPartialEnergy p M :=
    concrete_l2_graph_pair_partial_energy_nonneg_from_mono p M
  simpa [add_comm, add_left_comm, add_assoc] using
    (le_add_of_nonneg_left hnonneg :
      concreteL2GraphPairBlockEnergy p M K ≤
        concreteL2GraphPairPartialEnergy p M + concreteL2GraphPairBlockEnergy p M K)

/-- Any upper bound for a later partial energy is also an upper bound for the
corresponding finite block energy. -/
theorem concrete_l2_graph_pair_block_energy_le_of_later_partial_energy_le
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) {C : ℝ}
    (hC : concreteL2GraphPairPartialEnergy p (M + K) ≤ C) :
    concreteL2GraphPairBlockEnergy p M K ≤ C :=
  le_trans (concrete_l2_graph_pair_block_energy_le_later_partial_energy p M K) hC

/-- A uniform finite partial-energy upper bound gives a uniform finite block-energy
upper bound at every start and width. -/
theorem concrete_l2_graph_pair_block_energy_le_of_uniform_partial_energy_le
    (p : ConcreteL2GraphPairSpace) {C : ℝ}
    (hC : ∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C)
    (M K : ℕ) :
    concreteL2GraphPairBlockEnergy p M K ≤ C :=
  concrete_l2_graph_pair_block_energy_le_of_later_partial_energy_le p M K (hC (M + K))

/-- Adapter predicate for finite-tail bounds. -/
def concreteL2R2GraphPairFiniteTailBoundsAdapter : Prop :=
  ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairBlockEnergy p M K =
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ∧
    concreteL2GraphPairBlockEnergy p M K ≤
      concreteL2GraphPairPartialEnergy p (M + K)

/-- Adapter theorem for finite-tail bounds. -/
theorem concrete_l2_r2_graph_pair_finite_tail_bounds_adapter_ready :
    concreteL2R2GraphPairFiniteTailBoundsAdapter := by
  intro p M K
  exact ⟨
    concrete_l2_graph_pair_block_energy_eq_partial_energy_sub p M K,
    concrete_l2_graph_pair_block_energy_le_later_partial_energy p M K⟩

/-- R2r finite-tail bounds surface.

This layer converts finite telescoping into reusable finite tail bounds.  It is
still purely finite: no tail convergence, no Cauchy criterion, no infinite graph
norm, no graph-norm density, no closed operator theorem, no self-adjointness, and
no spectral theorem/PVM/positive-weight claim. -/
structure ConcreteL2R2GraphPairFiniteTailBoundsSurface where
  finiteTailTelescopingReady : concreteAnalyticSpineL2R2GraphPairFiniteTailTelescopingSurfaceReady
  blockEnergyAsIncrement :
    ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
      concreteL2GraphPairBlockEnergy p M K =
        concreteL2GraphPairPartialEnergy p (M + K) -
          concreteL2GraphPairPartialEnergy p M
  finiteBlockLeLaterPartial :
    ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
      concreteL2GraphPairBlockEnergy p M K ≤
        concreteL2GraphPairPartialEnergy p (M + K)
  uniformPartialBoundGivesBlockBound :
    ∀ (p : ConcreteL2GraphPairSpace) {C : ℝ},
      (∀ N : ℕ, concreteL2GraphPairPartialEnergy p N ≤ C) →
      ∀ M K : ℕ, concreteL2GraphPairBlockEnergy p M K ≤ C
  boundaryNotTailLimit : Prop
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

/-- Concrete R2r finite-tail bounds surface. -/
def concreteL2R2GraphPairFiniteTailBoundsSurface :
    ConcreteL2R2GraphPairFiniteTailBoundsSurface :=
  { finiteTailTelescopingReady :=
      concrete_analytic_spine_l2_r2_graph_pair_finite_tail_telescoping_surface_ready
    blockEnergyAsIncrement := concrete_l2_graph_pair_block_energy_eq_partial_energy_sub
    finiteBlockLeLaterPartial := concrete_l2_graph_pair_block_energy_le_later_partial_energy
    uniformPartialBoundGivesBlockBound := by
      intro p C hC M K
      exact concrete_l2_graph_pair_block_energy_le_of_uniform_partial_energy_le p hC M K
    boundaryNotTailLimit := True
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

/-- R2r readiness. -/
def concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairFiniteTailTelescopingSurfaceReady ∧
  concreteL2R2GraphPairFiniteTailBoundsAdapter ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotTailLimit ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotCauchyCriterion ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairFiniteTailBoundsSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2r. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_finite_tail_bounds_surface_ready :
    concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_finite_tail_telescoping_surface_ready <|
      And.intro concrete_l2_r2_graph_pair_finite_tail_bounds_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial trivial

/-- Boundary marker for R2r. -/
def concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsSurfaceReady

/-- Boundary theorem for R2r. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_finite_tail_bounds_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairFiniteTailBoundsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_finite_tail_bounds_surface_ready

end

end MathlibAnalytic
end MGAP4D
