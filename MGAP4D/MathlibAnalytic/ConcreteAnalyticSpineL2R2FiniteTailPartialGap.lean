import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteTailBoundScaffold

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- A finite tail bound controls the forward partial-energy gap from the same
start index. -/
theorem concrete_l2_graph_pair_finite_tail_bound_controls_forward_gap
    {p : ConcreteL2GraphPairSpace} {M : ℕ} {ε : ℝ}
    (h : concreteL2GraphPairFiniteTailBound p M ε) (K : ℕ) :
    concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M ≤ ε := by
  rw [← concrete_l2_graph_pair_block_energy_eq_partial_sub]
  exact h K

/-- A finite tail bound controls forward gaps from every later start index. -/
theorem concrete_l2_graph_pair_finite_tail_bound_controls_later_forward_gap
    {p : ConcreteL2GraphPairSpace} {M : ℕ} {ε : ℝ}
    (h : concreteL2GraphPairFiniteTailBound p M ε) (K L : ℕ) :
    concreteL2GraphPairPartialEnergy p (M + K + L) -
      concreteL2GraphPairPartialEnergy p (M + K) ≤ ε := by
  rw [← concrete_l2_graph_pair_block_energy_eq_partial_sub]
  exact concrete_l2_graph_pair_finite_tail_bound_controls_later_block h K L

/-- The zero graph pair has zero forward partial-energy gap. -/
theorem concrete_l2_graph_pair_zero_forward_gap_eq_zero
    (M K : ℕ) :
    concreteL2GraphPairPartialEnergy concreteL2GraphPairZero (M + K) -
      concreteL2GraphPairPartialEnergy concreteL2GraphPairZero M = 0 := by
  rw [← concrete_l2_graph_pair_block_energy_eq_partial_sub]
  exact concrete_l2_graph_pair_block_energy_zero_pair M K

/-- Forward partial-energy gaps are nonnegative. -/
theorem concrete_l2_graph_pair_forward_gap_nonneg
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M := by
  exact concrete_l2_graph_pair_partial_energy_forward_sub_nonneg p M K

/-- Finite-tail Cauchy scaffold controls later forward partial-energy gaps at
every positive tolerance. -/
theorem concrete_l2_graph_pair_finite_tail_scaffold_forward_gap_control
    {p : ConcreteL2GraphPairSpace}
    (h : concreteL2GraphPairFiniteTailCauchyScaffold p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ K L : ℕ,
      concreteL2GraphPairPartialEnergy p (M + K + L) -
        concreteL2GraphPairPartialEnergy p (M + K) ≤ ε := by
  rcases h ε hε with ⟨M, hM⟩
  exact ⟨M, fun K L =>
    concrete_l2_graph_pair_finite_tail_bound_controls_later_forward_gap hM K L⟩

/-- R2s finite-tail/partial-gap surface.  This turns the finite block-tail
predicate into forward partial-energy gap control.  It still does not assert the
general Cauchy theorem, an infinite graph norm, graph-norm topology, closed
operator, self-adjointness, spectral theorem application, PVM construction, or
positive spectral weight. -/
structure ConcreteL2R2FiniteTailPartialGapSurface where
  r2rReady : concreteAnalyticSpineL2R2FiniteTailBoundScaffoldSurfaceReady
  tailControlsForwardGap : ∀ {p : ConcreteL2GraphPairSpace} {M : ℕ} {ε : ℝ},
    concreteL2GraphPairFiniteTailBound p M ε → ∀ K : ℕ,
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ ε
  tailControlsLaterForwardGap : ∀ {p : ConcreteL2GraphPairSpace} {M : ℕ} {ε : ℝ},
    concreteL2GraphPairFiniteTailBound p M ε → ∀ K L : ℕ,
      concreteL2GraphPairPartialEnergy p (M + K + L) -
        concreteL2GraphPairPartialEnergy p (M + K) ≤ ε
  zeroForwardGapEqZero : ∀ (M K : ℕ),
    concreteL2GraphPairPartialEnergy concreteL2GraphPairZero (M + K) -
      concreteL2GraphPairPartialEnergy concreteL2GraphPairZero M = 0
  forwardGapNonneg : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M
  scaffoldForwardGapControl : ∀ {p : ConcreteL2GraphPairSpace},
    concreteL2GraphPairFiniteTailCauchyScaffold p → ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, ∀ K L : ℕ,
        concreteL2GraphPairPartialEnergy p (M + K + L) -
          concreteL2GraphPairPartialEnergy p (M + K) ≤ ε
  boundaryNotGeneralCauchyTheorem : Prop
  boundaryNotTailLimit : Prop
  boundaryNotInfiniteGraphNorm : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2s finite-tail/partial-gap surface. -/
def concreteL2R2FiniteTailPartialGapSurface :
    ConcreteL2R2FiniteTailPartialGapSurface :=
  { r2rReady := concrete_analytic_spine_l2_r2_finite_tail_bound_scaffold_surface_ready
    tailControlsForwardGap := fun h K =>
      concrete_l2_graph_pair_finite_tail_bound_controls_forward_gap h K
    tailControlsLaterForwardGap := fun h K L =>
      concrete_l2_graph_pair_finite_tail_bound_controls_later_forward_gap h K L
    zeroForwardGapEqZero := concrete_l2_graph_pair_zero_forward_gap_eq_zero
    forwardGapNonneg := concrete_l2_graph_pair_forward_gap_nonneg
    scaffoldForwardGapControl := fun h ε hε =>
      concrete_l2_graph_pair_finite_tail_scaffold_forward_gap_control h ε hε
    boundaryNotGeneralCauchyTheorem := True
    boundaryNotTailLimit := True
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
def concreteAnalyticSpineL2R2FiniteTailPartialGapSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2FiniteTailBoundScaffoldSurfaceReady ∧
  (∀ {p : ConcreteL2GraphPairSpace} {M : ℕ} {ε : ℝ},
    concreteL2GraphPairFiniteTailBound p M ε → ∀ K : ℕ,
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M ≤ ε) ∧
  (∀ {p : ConcreteL2GraphPairSpace} {M : ℕ} {ε : ℝ},
    concreteL2GraphPairFiniteTailBound p M ε → ∀ K L : ℕ,
      concreteL2GraphPairPartialEnergy p (M + K + L) -
        concreteL2GraphPairPartialEnergy p (M + K) ≤ ε) ∧
  (∀ (M K : ℕ),
    concreteL2GraphPairPartialEnergy concreteL2GraphPairZero (M + K) -
      concreteL2GraphPairPartialEnergy concreteL2GraphPairZero M = 0) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M) ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotGeneralCauchyTheorem ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotTailLimit ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotPVMConstruction ∧
  concreteL2R2FiniteTailPartialGapSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2s. -/
theorem concrete_analytic_spine_l2_r2_finite_tail_partial_gap_surface_ready :
    concreteAnalyticSpineL2R2FiniteTailPartialGapSurfaceReady := by
  unfold concreteAnalyticSpineL2R2FiniteTailPartialGapSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_finite_tail_bound_scaffold_surface_ready <|
      And.intro (fun h K =>
        concrete_l2_graph_pair_finite_tail_bound_controls_forward_gap h K) <|
        And.intro (fun h K L =>
          concrete_l2_graph_pair_finite_tail_bound_controls_later_forward_gap h K L) <|
          And.intro concrete_l2_graph_pair_zero_forward_gap_eq_zero <|
            And.intro concrete_l2_graph_pair_forward_gap_nonneg <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial <| And.intro trivial <| And.intro trivial <|
                    And.intro trivial trivial

/-- Boundary marker for R2s. -/
def concreteAnalyticSpineL2R2FiniteTailPartialGapHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2FiniteTailPartialGapSurfaceReady

/-- Boundary theorem for R2s. -/
theorem concrete_analytic_spine_l2_r2_finite_tail_partial_gap_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2FiniteTailPartialGapHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_finite_tail_partial_gap_surface_ready

end

end MathlibAnalytic
end MGAP4D
