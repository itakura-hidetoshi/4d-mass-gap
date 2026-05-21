import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairPartialEnergySurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp BigOperators

noncomputable section

/-- The zero cut-off of the finite graph-pair energy is zero. -/
theorem concrete_l2_graph_pair_partial_energy_zero_cutoff
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairPartialEnergy p 0 = 0 := by
  unfold concreteL2GraphPairPartialEnergy
  simp

/-- Successor-shell decomposition for finite graph-pair energy.  This is the
finite-energy analogue of adding one more square-energy shell. -/
theorem concrete_l2_graph_pair_partial_energy_succ_eq
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairPartialEnergy p (N + 1) =
      concreteL2GraphPairPartialEnergy p N + concreteL2GraphPairEnergyTerm p N := by
  unfold concreteL2GraphPairPartialEnergy
  rw [Finset.sum_range_succ]

/-- The first finite graph-pair energy cut-off is exactly the zeroth energy
shell. -/
theorem concrete_l2_graph_pair_partial_energy_one_eq
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairPartialEnergy p 1 = concreteL2GraphPairEnergyTerm p 0 := by
  simpa using concrete_l2_graph_pair_partial_energy_succ_eq p 0

/-- The successor shell is nonnegative. -/
theorem concrete_l2_graph_pair_partial_energy_shell_nonneg
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    0 ≤ concreteL2GraphPairEnergyTerm p N := by
  exact concrete_l2_graph_pair_energy_term_nonneg p N

/-- The successor-shell decomposition recovers monotonicity directly. -/
theorem concrete_l2_graph_pair_partial_energy_le_succ_from_shell
    (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairPartialEnergy p N ≤
      concreteL2GraphPairPartialEnergy p (N + 1) := by
  rw [concrete_l2_graph_pair_partial_energy_succ_eq]
  exact le_add_of_nonneg_right
    (concrete_l2_graph_pair_partial_energy_shell_nonneg p N)

/-- Zero pair has zero successor shell. -/
theorem concrete_l2_graph_pair_zero_shell
    (N : ℕ) :
    concreteL2GraphPairEnergyTerm concreteL2GraphPairZero N = 0 := by
  exact concrete_l2_graph_pair_energy_zero_ext N

/-- Scalar law for the successor shell. -/
theorem concrete_l2_graph_pair_shell_smul_eq
    (c : ℝ) (p : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) N =
      (c ^ 2) • concreteL2GraphPairEnergyTerm p N := by
  exact concrete_l2_graph_pair_energy_smul_eq c p N

/-- Add-estimate for the successor shell. -/
theorem concrete_l2_graph_pair_shell_add_le
    (p q : ConcreteL2GraphPairSpace) (N : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) N ≤
      (2 : ℝ) • concreteL2GraphPairEnergyTerm p N +
        (2 : ℝ) • concreteL2GraphPairEnergyTerm q N := by
  exact concrete_l2_graph_pair_energy_add_le p q N

/-- R2n graph-pair partial-energy shell surface.  This layer records the finite
successor decomposition `E_{N+1}=E_N+e_N`, preparing later Cauchy/limit work
without yet claiming an infinite graph norm or any operator/spectral promotion. -/
structure ConcreteL2R2GraphPairPartialEnergyShellSurface where
  r2mReady : concreteAnalyticSpineL2R2GraphPairPartialEnergySurfaceReady
  zeroCutoff : ∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphPairPartialEnergy p 0 = 0
  successorShell : ∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy p (N + 1) =
      concreteL2GraphPairPartialEnergy p N + concreteL2GraphPairEnergyTerm p N
  firstShell : ∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphPairPartialEnergy p 1 = concreteL2GraphPairEnergyTerm p 0
  shellNonneg : ∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    0 ≤ concreteL2GraphPairEnergyTerm p N
  monotoneFromShell : ∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy p N ≤
      concreteL2GraphPairPartialEnergy p (N + 1)
  zeroShell : ∀ N : ℕ,
    concreteL2GraphPairEnergyTerm concreteL2GraphPairZero N = 0
  shellSmulLaw : ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) N =
      (c ^ 2) • concreteL2GraphPairEnergyTerm p N
  shellAddEstimate : ∀ (p q : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) N ≤
      (2 : ℝ) • concreteL2GraphPairEnergyTerm p N +
        (2 : ℝ) • concreteL2GraphPairEnergyTerm q N
  boundaryNotInfiniteGraphNorm : Prop
  boundaryNotCauchyCriterion : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2n graph-pair partial-energy shell surface. -/
def concreteL2R2GraphPairPartialEnergyShellSurface :
    ConcreteL2R2GraphPairPartialEnergyShellSurface :=
  { r2mReady := concrete_analytic_spine_l2_r2_graph_pair_partial_energy_surface_ready
    zeroCutoff := concrete_l2_graph_pair_partial_energy_zero_cutoff
    successorShell := concrete_l2_graph_pair_partial_energy_succ_eq
    firstShell := concrete_l2_graph_pair_partial_energy_one_eq
    shellNonneg := concrete_l2_graph_pair_partial_energy_shell_nonneg
    monotoneFromShell := concrete_l2_graph_pair_partial_energy_le_succ_from_shell
    zeroShell := concrete_l2_graph_pair_zero_shell
    shellSmulLaw := concrete_l2_graph_pair_shell_smul_eq
    shellAddEstimate := concrete_l2_graph_pair_shell_add_le
    boundaryNotInfiniteGraphNorm := True
    boundaryNotCauchyCriterion := True
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2n readiness. -/
def concreteAnalyticSpineL2R2GraphPairPartialEnergyShellSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairPartialEnergySurfaceReady ∧
  (∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphPairPartialEnergy p 0 = 0) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy p (N + 1) =
      concreteL2GraphPairPartialEnergy p N + concreteL2GraphPairEnergyTerm p N) ∧
  (∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphPairPartialEnergy p 1 = concreteL2GraphPairEnergyTerm p 0) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    0 ≤ concreteL2GraphPairEnergyTerm p N) ∧
  (∀ (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairPartialEnergy p N ≤
      concreteL2GraphPairPartialEnergy p (N + 1)) ∧
  (∀ N : ℕ, concreteL2GraphPairEnergyTerm concreteL2GraphPairZero N = 0) ∧
  (∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) N =
      (c ^ 2) • concreteL2GraphPairEnergyTerm p N) ∧
  (∀ (p q : ConcreteL2GraphPairSpace) (N : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) N ≤
      (2 : ℝ) • concreteL2GraphPairEnergyTerm p N +
        (2 : ℝ) • concreteL2GraphPairEnergyTerm q N) ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotInfiniteGraphNorm ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotCauchyCriterion ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairPartialEnergyShellSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2n. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_partial_energy_shell_surface_ready :
    concreteAnalyticSpineL2R2GraphPairPartialEnergyShellSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairPartialEnergyShellSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_partial_energy_surface_ready <|
      And.intro concrete_l2_graph_pair_partial_energy_zero_cutoff <|
        And.intro concrete_l2_graph_pair_partial_energy_succ_eq <|
          And.intro concrete_l2_graph_pair_partial_energy_one_eq <|
            And.intro concrete_l2_graph_pair_partial_energy_shell_nonneg <|
              And.intro concrete_l2_graph_pair_partial_energy_le_succ_from_shell <|
                And.intro concrete_l2_graph_pair_zero_shell <|
                  And.intro concrete_l2_graph_pair_shell_smul_eq <|
                    And.intro concrete_l2_graph_pair_shell_add_le <|
                      And.intro trivial <| And.intro trivial <| And.intro trivial <|
                        And.intro trivial <| And.intro trivial <| And.intro trivial <|
                          And.intro trivial <| And.intro trivial <|
                            And.intro trivial trivial

/-- Boundary marker for R2n. -/
def concreteAnalyticSpineL2R2GraphPairPartialEnergyShellHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairPartialEnergyShellSurfaceReady

/-- Boundary theorem for R2n. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_partial_energy_shell_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairPartialEnergyShellHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_partial_energy_shell_surface_ready

end

end MathlibAnalytic
end MGAP4D
