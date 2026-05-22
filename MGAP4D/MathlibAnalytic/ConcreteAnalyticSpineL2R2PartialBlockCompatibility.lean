import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairBlockEnergy

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- Compatibility between partial energy and finite block energy: the partial
energy through `M + K` is the head partial energy through `M` plus the block of
`K` shells starting at `M`. -/
theorem concrete_l2_graph_pair_partial_energy_add_eq_partial_add_block
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairPartialEnergy p (M + K) =
      concreteL2GraphPairPartialEnergy p M +
        concreteL2GraphPairBlockEnergy p M K := by
  induction K with
  | zero =>
      simp [concrete_l2_graph_pair_block_energy_zero_width]
  | succ K ih =>
      have hNat : M + (K + 1) = M + K + 1 := by
        rw [Nat.add_assoc]
      rw [hNat, concrete_l2_graph_pair_partial_energy_succ_eq,
        concrete_l2_graph_pair_block_energy_succ_eq, ih]
      ring

/-- The block energy is the difference of two finite partial energies.  This is
only a finite algebraic identity; it is not an infinite tail limit. -/
theorem concrete_l2_graph_pair_block_energy_eq_partial_sub
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairBlockEnergy p M K =
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M := by
  have h := concrete_l2_graph_pair_partial_energy_add_eq_partial_add_block p M K
  rw [h]
  ring

/-- Finite partial-energy differences are nonnegative in the forward direction. -/
theorem concrete_l2_graph_pair_partial_energy_forward_sub_nonneg
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M := by
  rw [← concrete_l2_graph_pair_block_energy_eq_partial_sub]
  exact concrete_l2_graph_pair_block_energy_nonneg p M K

/-- Finite partial energies are monotone along additive extensions. -/
theorem concrete_l2_graph_pair_partial_energy_le_add_right
    (p : ConcreteL2GraphPairSpace) (M K : ℕ) :
    concreteL2GraphPairPartialEnergy p M ≤
      concreteL2GraphPairPartialEnergy p (M + K) := by
  rw [concrete_l2_graph_pair_partial_energy_add_eq_partial_add_block]
  exact le_add_of_nonneg_right (concrete_l2_graph_pair_block_energy_nonneg p M K)

/-- Zero-width compatibility specializes to identity. -/
theorem concrete_l2_graph_pair_partial_energy_add_zero_compat
    (p : ConcreteL2GraphPairSpace) (M : ℕ) :
    concreteL2GraphPairPartialEnergy p (M + 0) =
      concreteL2GraphPairPartialEnergy p M := by
  simp

/-- R2p partial/block compatibility surface.  This is the first finite
head-plus-block algebra for the graph-pair energy.  It deliberately stops before
any infinite tail/Cauchy criterion, graph-norm topology, closed operator,
self-adjointness, spectral theorem application, PVM construction, or positive
spectral-weight theorem. -/
structure ConcreteL2R2PartialBlockCompatibilitySurface where
  r2oReady : concreteAnalyticSpineL2R2GraphPairBlockEnergySurfaceReady
  partialAddBlock : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairPartialEnergy p (M + K) =
      concreteL2GraphPairPartialEnergy p M +
        concreteL2GraphPairBlockEnergy p M K
  blockEqPartialSub : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairBlockEnergy p M K =
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M
  forwardSubNonneg : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M
  partialLeAddRight : ∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairPartialEnergy p M ≤
      concreteL2GraphPairPartialEnergy p (M + K)
  addZeroCompat : ∀ (p : ConcreteL2GraphPairSpace) (M : ℕ),
    concreteL2GraphPairPartialEnergy p (M + 0) =
      concreteL2GraphPairPartialEnergy p M
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

/-- Concrete R2p partial/block compatibility surface. -/
def concreteL2R2PartialBlockCompatibilitySurface :
    ConcreteL2R2PartialBlockCompatibilitySurface :=
  { r2oReady := concrete_analytic_spine_l2_r2_graph_pair_block_energy_surface_ready
    partialAddBlock := concrete_l2_graph_pair_partial_energy_add_eq_partial_add_block
    blockEqPartialSub := concrete_l2_graph_pair_block_energy_eq_partial_sub
    forwardSubNonneg := concrete_l2_graph_pair_partial_energy_forward_sub_nonneg
    partialLeAddRight := concrete_l2_graph_pair_partial_energy_le_add_right
    addZeroCompat := concrete_l2_graph_pair_partial_energy_add_zero_compat
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

/-- R2p readiness. -/
def concreteAnalyticSpineL2R2PartialBlockCompatibilitySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairBlockEnergySurfaceReady ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairPartialEnergy p (M + K) =
      concreteL2GraphPairPartialEnergy p M +
        concreteL2GraphPairBlockEnergy p M K) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairBlockEnergy p M K =
      concreteL2GraphPairPartialEnergy p (M + K) -
        concreteL2GraphPairPartialEnergy p M) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    0 ≤ concreteL2GraphPairPartialEnergy p (M + K) -
      concreteL2GraphPairPartialEnergy p M) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M K : ℕ),
    concreteL2GraphPairPartialEnergy p M ≤
      concreteL2GraphPairPartialEnergy p (M + K)) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (M : ℕ),
    concreteL2GraphPairPartialEnergy p (M + 0) =
      concreteL2GraphPairPartialEnergy p M) ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotTailLimit ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotCauchyCriterion ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotGraphNormTopology ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotSelfAdjointness ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotPVMConstruction ∧
  concreteL2R2PartialBlockCompatibilitySurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2p. -/
theorem concrete_analytic_spine_l2_r2_partial_block_compatibility_surface_ready :
    concreteAnalyticSpineL2R2PartialBlockCompatibilitySurfaceReady := by
  unfold concreteAnalyticSpineL2R2PartialBlockCompatibilitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_block_energy_surface_ready <|
      And.intro concrete_l2_graph_pair_partial_energy_add_eq_partial_add_block <|
        And.intro concrete_l2_graph_pair_block_energy_eq_partial_sub <|
          And.intro concrete_l2_graph_pair_partial_energy_forward_sub_nonneg <|
            And.intro concrete_l2_graph_pair_partial_energy_le_add_right <|
              And.intro concrete_l2_graph_pair_partial_energy_add_zero_compat <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial <| And.intro trivial <| And.intro trivial <|
                    And.intro trivial <| And.intro trivial <| And.intro trivial <|
                      And.intro trivial trivial

/-- Boundary marker for R2p. -/
def concreteAnalyticSpineL2R2PartialBlockCompatibilityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2PartialBlockCompatibilitySurfaceReady

/-- Boundary theorem for R2p. -/
theorem concrete_analytic_spine_l2_r2_partial_block_compatibility_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2PartialBlockCompatibilityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_partial_block_compatibility_surface_ready

end

end MathlibAnalytic
end MGAP4D
