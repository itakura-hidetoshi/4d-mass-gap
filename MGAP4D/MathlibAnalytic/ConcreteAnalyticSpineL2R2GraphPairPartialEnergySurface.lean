import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergySurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- Finite graph-pair energy cut-off.  This is the Mathlib finite-sum layer
sitting between the pointwise square-energy term and any later graph-norm or
infinite-series norm construction. -/
def concreteL2GraphPairPartialEnergy (p : ConcreteL2GraphPairSpace) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun n => concreteL2GraphPairEnergyTerm p n)

/-- Every finite graph-pair energy cut-off is nonnegative. -/
theorem concrete_l2_graph_pair_partial_energy_nonneg
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    0 ≤ concreteL2GraphPairPartialEnergy p N := by
  unfold concreteL2GraphPairPartialEnergy
  exact Finset.sum_nonneg fun n _ => concrete_l2_graph_pair_energy_term_nonneg p n

/-- The zero graph pair has zero finite graph-pair energy at every cut-off. -/
theorem concrete_l2_graph_pair_partial_energy_zero
    (N : ℕ) :
    concreteL2GraphPairPartialEnergy concreteL2GraphPairZero N = 0 := by
  unfold concreteL2GraphPairPartialEnergy
  simp [concrete_l2_graph_pair_energy_zero_ext]

/-- The finite graph-pair energy cut-offs form an increasing sequence. -/
theorem concrete_l2_graph_pair_partial_energy_succ_monotone
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairPartialEnergy p N ≤
      concreteL2GraphPairPartialEnergy p (N + 1) := by
  unfold concreteL2GraphPairPartialEnergy
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (concrete_l2_graph_pair_energy_term_nonneg p N)

/-- Finite add-energy estimate obtained by summing the pointwise estimate. -/
theorem concrete_l2_graph_pair_partial_energy_add_le
    (p q : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairPartialEnergy (concreteL2GraphPairAdd p q) N ≤
      (2 : ℝ) • concreteL2GraphPairPartialEnergy p N +
        (2 : ℝ) • concreteL2GraphPairPartialEnergy q N := by
  unfold concreteL2GraphPairPartialEnergy
  have hsum :
      Finset.sum (Finset.range N)
          (fun n => concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n) ≤
        Finset.sum (Finset.range N)
          (fun n =>
            (2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
              (2 : ℝ) • concreteL2GraphPairEnergyTerm q n) := by
    exact Finset.sum_le_sum fun n _ => concrete_l2_graph_pair_energy_add_le p q n
  have hsplit :
      Finset.sum (Finset.range N)
          (fun n =>
            (2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
              (2 : ℝ) • concreteL2GraphPairEnergyTerm q n) =
        (2 : ℝ) •
            Finset.sum (Finset.range N)
              (fun n => concreteL2GraphPairEnergyTerm p n) +
          (2 : ℝ) •
            Finset.sum (Finset.range N)
              (fun n => concreteL2GraphPairEnergyTerm q n) := by
    simp [Finset.sum_add_distrib, Finset.smul_sum]
  exact hsum.trans_eq hsplit

/-- Finite scalar-energy law: the cut-off energy scales by `c^2`. -/
theorem concrete_l2_graph_pair_partial_energy_smul_eq
    (c : ℝ) (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairPartialEnergy (concreteL2GraphPairSmul c p) N =
      (c ^ 2) • concreteL2GraphPairPartialEnergy p N := by
  unfold concreteL2GraphPairPartialEnergy
  calc
    Finset.sum (Finset.range N)
        (fun n => concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) n) =
        Finset.sum (Finset.range N)
          (fun n => (c ^ 2) • concreteL2GraphPairEnergyTerm p n) := by
      exact Finset.sum_congr rfl fun n _ => concrete_l2_graph_pair_energy_smul_eq c p n
    _ = (c ^ 2) •
          Finset.sum (Finset.range N) (fun n => concreteL2GraphPairEnergyTerm p n) := by
      exact (Finset.smul_sum
        (s := Finset.range N)
        (f := fun n : ℕ => concreteL2GraphPairEnergyTerm p n)
        (a := c ^ 2)).symm

/-- R2m graph-pair partial-energy surface.  This layer converts the pointwise
energy estimates into Mathlib finite-sum estimates.  It is intentionally still a
finite cut-off surface, not an infinite graph norm, closed-operator theorem,
self-adjointness theorem, spectral theorem application, PVM construction, or
positive spectral-weight theorem. -/
structure ConcreteL2R2GraphPairPartialEnergySurface where
  r2lReady : concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady
  partialEnergy : ConcreteL2GraphPairSpace → ℕ → ℝ
  partialEnergy_eq : partialEnergy = concreteL2GraphPairPartialEnergy
  partialEnergyNonneg : ∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    0 ≤ partialEnergy p N
  zeroPartialEnergy : ∀ N : ℕ, partialEnergy concreteL2GraphPairZero N = 0
  partialEnergySuccMonotone : ∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    partialEnergy p N ≤ partialEnergy p (N + 1)
  partialAddEnergyEstimate : ∀ (p q : ConcreteL2GraphPairSpace) (N : ℕ),
    partialEnergy (concreteL2GraphPairAdd p q) N ≤
      (2 : ℝ) • partialEnergy p N + (2 : ℝ) • partialEnergy q N
  partialSmulEnergyLaw : ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (N : ℕ),
    partialEnergy (concreteL2GraphPairSmul c p) N = (c ^ 2) • partialEnergy p N
  boundaryNotInfiniteGraphNorm : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2m graph-pair partial-energy surface. -/
def concreteL2R2GraphPairPartialEnergySurface :
    ConcreteL2R2GraphPairPartialEnergySurface :=
  { r2lReady := concrete_analytic_spine_l2_r2_graph_pair_energy_surface_ready
    partialEnergy := concreteL2GraphPairPartialEnergy
    partialEnergy_eq := rfl
    partialEnergyNonneg := concrete_l2_graph_pair_partial_energy_nonneg
    zeroPartialEnergy := concrete_l2_graph_pair_partial_energy_zero
    partialEnergySuccMonotone := concrete_l2_graph_pair_partial_energy_succ_monotone
    partialAddEnergyEstimate := concrete_l2_graph_pair_partial_energy_add_le
    partialSmulEnergyLaw := concrete_l2_graph_pair_partial_energy_smul_eq
    boundaryNotInfiniteGraphNorm := True
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2m readiness: pointwise graph-pair energy has been lifted to finite
Mathlib partial sums, with nonnegativity, zero, monotonicity, add-estimate, and
scalar law preserved. -/
def concreteAnalyticSpineL2R2GraphPairPartialEnergySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady ∧
  (∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    0 ≤ concreteL2GraphPairPartialEnergy p N) ∧
  (∀ N : ℕ, concreteL2GraphPairPartialEnergy concreteL2GraphPairZero N = 0) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy p N ≤
      concreteL2GraphPairPartialEnergy p (N + 1)) ∧
  (∀ (p q : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy (concreteL2GraphPairAdd p q) N ≤
      (2 : ℝ) • concreteL2GraphPairPartialEnergy p N +
        (2 : ℝ) • concreteL2GraphPairPartialEnergy q N) ∧
  (∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy (concreteL2GraphPairSmul c p) N =
      (c ^ 2) • concreteL2GraphPairPartialEnergy p N) ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairPartialEnergySurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2m. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_partial_energy_surface_ready :
    concreteAnalyticSpineL2R2GraphPairPartialEnergySurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairPartialEnergySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_surface_ready <|
      And.intro concrete_l2_graph_pair_partial_energy_nonneg <|
        And.intro concrete_l2_graph_pair_partial_energy_zero <|
          And.intro concrete_l2_graph_pair_partial_energy_succ_monotone <|
            And.intro concrete_l2_graph_pair_partial_energy_add_le <|
              And.intro concrete_l2_graph_pair_partial_energy_smul_eq <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial <| And.intro trivial <| And.intro trivial <|
                    And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2m. -/
def concreteAnalyticSpineL2R2GraphPairPartialEnergyHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairPartialEnergySurfaceReady

/-- Boundary theorem for R2m. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_partial_energy_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairPartialEnergyHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_partial_energy_surface_ready

end

end MathlibAnalytic
end MGAP4D
