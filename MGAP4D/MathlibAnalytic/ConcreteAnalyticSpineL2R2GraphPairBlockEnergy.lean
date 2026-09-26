import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairPartialEnergyShell

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- Finite block energy starting at shell `M` and containing `K` shells.  This is
an interval-like finite energy without invoking any infinite tail limit. -/
def concreteL2GraphPairBlockEnergy
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) : ℝ :=
  Finset.sum (Finset.range K) (fun n => concreteL2GraphPairEnergyTerm p (M + n))

/-- Every finite block energy is nonnegative. -/
theorem concrete_l2_graph_pair_block_energy_nonneg
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    0 ≤ concreteL2GraphPairBlockEnergy p M K := by
  unfold concreteL2GraphPairBlockEnergy
  exact Finset.sum_nonneg fun n _ =>
    concrete_l2_graph_pair_energy_term_nonneg p (M + n)

/-- A block with zero width has zero energy. -/
theorem concrete_l2_graph_pair_block_energy_zero_width
    (p : ConcreteL2GraphPairSpace) (M : ℕ) :
    concreteL2GraphPairBlockEnergy p M 0 = 0 := by
  unfold concreteL2GraphPairBlockEnergy
  simp

/-- Successor-width decomposition for finite block energy. -/
theorem concrete_l2_graph_pair_block_energy_succ_eq
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairBlockEnergy p M (K + 1) =
      concreteL2GraphPairBlockEnergy p M K +
        concreteL2GraphPairEnergyTerm p (M + K) := by
  unfold concreteL2GraphPairBlockEnergy
  rw [Finset.sum_range_succ]

/-- The block energy starting at zero is the ordinary partial energy. -/
theorem concrete_l2_graph_pair_block_energy_zero_start_eq_partial
    (p : ConcreteL2GraphPairSpace) (K : ℕ) :
    concreteL2GraphPairBlockEnergy p 0 K = concreteL2GraphPairPartialEnergy p K := by
  unfold concreteL2GraphPairBlockEnergy concreteL2GraphPairPartialEnergy
  simp

/-- The zero graph pair has zero finite block energy. -/
theorem concrete_l2_graph_pair_block_energy_zero_pair
    (M K : ℕ) :
    concreteL2GraphPairBlockEnergy concreteL2GraphPairZero M K = 0 := by
  unfold concreteL2GraphPairBlockEnergy
  simp [concrete_l2_graph_pair_zero_shell]

/-- Finite block add-energy estimate. -/
theorem concrete_l2_graph_pair_block_energy_add_le
    (p q : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairBlockEnergy (concreteL2GraphPairAdd p q) M K ≤
      (2 : ℝ) • concreteL2GraphPairBlockEnergy p M K +
        (2 : ℝ) • concreteL2GraphPairBlockEnergy q M K := by
  unfold concreteL2GraphPairBlockEnergy
  have hsum :
      Finset.sum (Finset.range K)
          (fun n => concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) (M + n)) ≤
        Finset.sum (Finset.range K)
          (fun n =>
            (2 : ℝ) • concreteL2GraphPairEnergyTerm p (M + n) +
              (2 : ℝ) • concreteL2GraphPairEnergyTerm q (M + n)) := by
    exact Finset.sum_le_sum fun n _ =>
      concrete_l2_graph_pair_shell_add_le p q (M + n)
  have hsplit :
      Finset.sum (Finset.range K)
          (fun n =>
            (2 : ℝ) • concreteL2GraphPairEnergyTerm p (M + n) +
              (2 : ℝ) • concreteL2GraphPairEnergyTerm q (M + n)) =
        (2 : ℝ) •
            Finset.sum (Finset.range K)
              (fun n => concreteL2GraphPairEnergyTerm p (M + n)) +
          (2 : ℝ) •
            Finset.sum (Finset.range K)
              (fun n => concreteL2GraphPairEnergyTerm q (M + n)) := by
    simp [Finset.sum_add_distrib, smul_eq_mul, Finset.mul_sum]
  exact hsum.trans_eq hsplit

/-- Finite block scalar-energy law. -/
theorem concrete_l2_graph_pair_block_energy_smul_eq
    (c : ℝ) (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairBlockEnergy (concreteL2GraphPairSmul c p) M K =
      (c ^ 2) • concreteL2GraphPairBlockEnergy p M K := by
  unfold concreteL2GraphPairBlockEnergy
  calc
    Finset.sum (Finset.range K)
        (fun n => concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) (M + n)) =
        Finset.sum (Finset.range K)
          (fun n => (c ^ 2) • concreteL2GraphPairEnergyTerm p (M + n)) := by
      exact Finset.sum_congr rfl fun n _ =>
        concrete_l2_graph_pair_shell_smul_eq c p (M + n)
    _ = (c ^ 2) •
          Finset.sum (Finset.range K)
            (fun n => concreteL2GraphPairEnergyTerm p (M + n)) := by
      simp [smul_eq_mul, Finset.mul_sum]

/-- R2o graph-pair block-energy surface.  This is a finite interval-energy layer:
it prepares later tail/Cauchy arguments while still refusing every infinite
norm/topology/operator/spectral promotion. -/
structure ConcreteL2R2GraphPairBlockEnergySurface where
  r2nReady : concreteAnalyticSpineL2R2GraphPairPartialEnergyShellSurfaceReady
  blockEnergy : ConcreteL2GraphPairSpace → ℕ → ℕ → ℝ
  blockEnergy_eq : blockEnergy = concreteL2GraphPairBlockEnergy
  blockEnergyNonneg : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    0 ≤ blockEnergy p M K
  zeroWidth : ∀ (p : ConcreteL2GraphPairSpace) (M : ℕ),
    blockEnergy p M 0 = 0
  successorBlock : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    blockEnergy p M (K + 1) =
      blockEnergy p M K + concreteL2GraphPairEnergyTerm p (M + K)
  zeroStartEqPartial : ∀ (p : ConcreteL2GraphPairSpace) (K : ℕ),
    blockEnergy p 0 K = concreteL2GraphPairPartialEnergy p K
  zeroPairBlock : ∀ (M K : ℕ),
    blockEnergy concreteL2GraphPairZero M K = 0
  blockAddEstimate : ∀ (p q : ConcreteL2GraphPairSpace) (M K : ℕ),
    blockEnergy (concreteL2GraphPairAdd p q) M K ≤
      (2 : ℝ) • blockEnergy p M K + (2 : ℝ) • blockEnergy q M K
  blockSmulLaw : ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    blockEnergy (concreteL2GraphPairSmul c p) M K =
      (c ^ 2) • blockEnergy p M K
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

/-- Concrete R2o graph-pair block-energy surface. -/
def concreteL2R2GraphPairBlockEnergySurface :
    ConcreteL2R2GraphPairBlockEnergySurface :=
  { r2nReady := concrete_analytic_spine_l2_r2_graph_pair_partial_energy_shell_surface_ready
    blockEnergy := concreteL2GraphPairBlockEnergy
    blockEnergy_eq := rfl
    blockEnergyNonneg := concrete_l2_graph_pair_block_energy_nonneg
    zeroWidth := concrete_l2_graph_pair_block_energy_zero_width
    successorBlock := concrete_l2_graph_pair_block_energy_succ_eq
    zeroStartEqPartial := concrete_l2_graph_pair_block_energy_zero_start_eq_partial
    zeroPairBlock := concrete_l2_graph_pair_block_energy_zero_pair
    blockAddEstimate := concrete_l2_graph_pair_block_energy_add_le
    blockSmulLaw := concrete_l2_graph_pair_block_energy_smul_eq
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

/-- R2o readiness. -/
def concreteAnalyticSpineL2R2GraphPairBlockEnergySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairPartialEnergyShellSurfaceReady ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    0 ≤ concreteL2GraphPairBlockEnergy p M K) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M : ℕ),
    concreteL2GraphPairBlockEnergy p M 0 = 0) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairBlockEnergy p M (K + 1) =
      concreteL2GraphPairBlockEnergy p M K +
        concreteL2GraphPairEnergyTerm p (M + K)) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (K : ℕ),
    concreteL2GraphPairBlockEnergy p 0 K = concreteL2GraphPairPartialEnergy p K) ∧
  (∀ (M K : ℕ),
    concreteL2GraphPairBlockEnergy concreteL2GraphPairZero M K = 0) ∧
  (∀ (p q : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairBlockEnergy (concreteL2GraphPairAdd p q) M K ≤
      (2 : ℝ) • concreteL2GraphPairBlockEnergy p M K +
        (2 : ℝ) • concreteL2GraphPairBlockEnergy q M K) ∧
  (∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairBlockEnergy (concreteL2GraphPairSmul c p) M K =
      (c ^ 2) • concreteL2GraphPairBlockEnergy p M K) ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotTailLimit ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotCauchyCriterion ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairBlockEnergySurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2o. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_block_energy_surface_ready :
    concreteAnalyticSpineL2R2GraphPairBlockEnergySurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairBlockEnergySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_partial_energy_shell_surface_ready <|
      And.intro concrete_l2_graph_pair_block_energy_nonneg <|
        And.intro concrete_l2_graph_pair_block_energy_zero_width <|
          And.intro concrete_l2_graph_pair_block_energy_succ_eq <|
            And.intro concrete_l2_graph_pair_block_energy_zero_start_eq_partial <|
              And.intro concrete_l2_graph_pair_block_energy_zero_pair <|
                And.intro concrete_l2_graph_pair_block_energy_add_le <|
                  And.intro concrete_l2_graph_pair_block_energy_smul_eq <|
                    And.intro trivial <| And.intro trivial <| And.intro trivial <|
                      And.intro trivial <| And.intro trivial <| And.intro trivial <|
                        And.intro trivial <| And.intro trivial <| And.intro trivial <|
                          And.intro trivial trivial

/-- Boundary marker for R2o. -/
def concreteAnalyticSpineL2R2GraphPairBlockEnergyHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairBlockEnergySurfaceReady

/-- Boundary theorem for R2o. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_block_energy_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairBlockEnergyHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_block_energy_surface_ready

end

end MathlibAnalytic
end MGAP4D
