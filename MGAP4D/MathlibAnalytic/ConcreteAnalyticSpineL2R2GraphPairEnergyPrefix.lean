import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergySurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite prefix of the concrete graph-pair square-energy series.  This is a
finite pre-graph-norm bookkeeping surface, not a graph-norm topology. -/
def concreteL2GraphPairEnergyPrefix (N : ℕ) (p : ConcreteL2GraphPairSpace) : ℝ :=
  ∑ n in Finset.range N, concreteL2GraphPairEnergyTerm p n

/-- The finite graph-pair energy prefix is nonnegative. -/
theorem concrete_l2_graph_pair_energy_prefix_nonneg
    (N : ℕ) (p : ConcreteL2GraphPairSpace) :
    0 ≤ concreteL2GraphPairEnergyPrefix N p := by
  unfold concreteL2GraphPairEnergyPrefix
  exact Finset.sum_nonneg fun n _hn =>
    concrete_l2_graph_pair_energy_term_nonneg p n

/-- The zero graph pair has zero finite graph-pair energy prefix. -/
theorem concrete_l2_graph_pair_energy_prefix_zero
    (N : ℕ) :
    concreteL2GraphPairEnergyPrefix N concreteL2GraphPairZero = 0 := by
  simp [concreteL2GraphPairEnergyPrefix,
    concrete_l2_graph_pair_energy_zero_ext]

/-- Finite-prefix add-energy estimate for concrete graph pairs.  The right side
is intentionally kept as a finite sum of pointwise upper bounds; no graph-norm
triangle inequality is claimed here. -/
theorem concrete_l2_graph_pair_energy_prefix_add_le_sum_bound
    (N : ℕ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairAdd p q) ≤
      ∑ n in Finset.range N,
        ((2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
          (2 : ℝ) • concreteL2GraphPairEnergyTerm q n) := by
  unfold concreteL2GraphPairEnergyPrefix
  exact Finset.sum_le_sum fun n _hn =>
    concrete_l2_graph_pair_energy_add_le p q n

/-- Scalar finite-prefix energy is the finite sum of the pointwise scaled energy
law.  This is a finite prefix law, not yet a completed graph-norm law. -/
theorem concrete_l2_graph_pair_energy_prefix_smul_eq_sum
    (N : ℕ) (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul c p) =
      ∑ n in Finset.range N, (c ^ 2) • concreteL2GraphPairEnergyTerm p n := by
  unfold concreteL2GraphPairEnergyPrefix
  exact Finset.sum_congr rfl fun n _hn =>
    concrete_l2_graph_pair_energy_smul_eq c p n

/-- R2m finite graph-pair energy prefix surface. -/
structure ConcreteL2R2GraphPairEnergyPrefixSurface where
  r2lReady : concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady
  energyPrefix : ℕ → ConcreteL2GraphPairSpace → ℝ
  prefixNonneg : ∀ (N : ℕ) (p : ConcreteL2GraphPairSpace), 0 ≤ energyPrefix N p
  prefixZero : ∀ N : ℕ, energyPrefix N concreteL2GraphPairZero = 0
  prefixAddBound : ∀ (N : ℕ) (p q : ConcreteL2GraphPairSpace),
    energyPrefix N (concreteL2GraphPairAdd p q) ≤
      ∑ n in Finset.range N,
        ((2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
          (2 : ℝ) • concreteL2GraphPairEnergyTerm q n)
  prefixSmulLaw : ∀ (N : ℕ) (c : ℝ) (p : ConcreteL2GraphPairSpace),
    energyPrefix N (concreteL2GraphPairSmul c p) =
      ∑ n in Finset.range N, (c ^ 2) • concreteL2GraphPairEnergyTerm p n
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormTriangleInequality : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2m finite energy-prefix surface. -/
def concreteL2R2GraphPairEnergyPrefixSurface :
    ConcreteL2R2GraphPairEnergyPrefixSurface :=
  { r2lReady := concrete_analytic_spine_l2_r2_graph_pair_energy_surface_ready
    energyPrefix := concreteL2GraphPairEnergyPrefix
    prefixNonneg := concrete_l2_graph_pair_energy_prefix_nonneg
    prefixZero := concrete_l2_graph_pair_energy_prefix_zero
    prefixAddBound := concrete_l2_graph_pair_energy_prefix_add_le_sum_bound
    prefixSmulLaw := concrete_l2_graph_pair_energy_prefix_smul_eq_sum
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormTriangleInequality := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2m readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady ∧
  (∀ (N : ℕ) (p : ConcreteL2GraphPairSpace),
    0 ≤ concreteL2GraphPairEnergyPrefix N p) ∧
  (∀ N : ℕ,
    concreteL2GraphPairEnergyPrefix N concreteL2GraphPairZero = 0) ∧
  (∀ (N : ℕ) (p q : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairAdd p q) ≤
      ∑ n in Finset.range N,
        ((2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
          (2 : ℝ) • concreteL2GraphPairEnergyTerm q n)) ∧
  (∀ (N : ℕ) (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul c p) =
      ∑ n in Finset.range N, (c ^ 2) • concreteL2GraphPairEnergyTerm p n) ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotGraphNormTriangleInequality ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2m. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairEnergyPrefixSurfaceReady
  exact And.intro concrete_analytic_spine_l2_r2_graph_pair_energy_surface_ready <|
    And.intro concrete_l2_graph_pair_energy_prefix_nonneg <|
      And.intro concrete_l2_graph_pair_energy_prefix_zero <|
        And.intro concrete_l2_graph_pair_energy_prefix_add_le_sum_bound <|
          And.intro concrete_l2_graph_pair_energy_prefix_smul_eq_sum <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial trivial

/-- Boundary marker for R2m. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixSurfaceReady

/-- Boundary theorem for R2m. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_surface_ready

end

end MathlibAnalytic
end MGAP4D
