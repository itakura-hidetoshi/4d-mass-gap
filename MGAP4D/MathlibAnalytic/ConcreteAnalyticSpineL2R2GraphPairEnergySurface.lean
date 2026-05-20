import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Pointwise graph-pair energy on the concrete graph-pair carrier.  This is the
pre-graph-norm square-energy series term `fst^2 + snd^2`. -/
def concreteL2GraphPairEnergyTerm (p : ConcreteL2GraphPairSpace) (n : ℕ) : ℝ :=
  (concreteL2GraphPairFst p).1 n ^ 2 + (concreteL2GraphPairSnd p).1 n ^ 2

/-- The graph-pair energy term is pointwise nonnegative. -/
theorem concrete_l2_graph_pair_energy_term_nonneg
    (p : ConcreteL2GraphPairSpace) (n : ℕ) :
    0 ≤ concreteL2GraphPairEnergyTerm p n := by
  unfold concreteL2GraphPairEnergyTerm
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Every concrete graph pair has summable square-energy series. -/
theorem concrete_l2_graph_pair_energy_summable
    (p : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ => concreteL2GraphPairEnergyTerm p n := by
  unfold concreteL2GraphPairEnergyTerm
  exact (concreteL2GraphPairFst p).2.add (concreteL2GraphPairSnd p).2

/-- The zero graph pair has zero graph-pair energy pointwise. -/
theorem concrete_l2_graph_pair_energy_zero_ext (n : ℕ) :
    concreteL2GraphPairEnergyTerm concreteL2GraphPairZero n = 0 := by
  simp [concreteL2GraphPairEnergyTerm, concreteL2GraphPairZero,
    concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealZero]

/-- Pointwise add-energy estimate for concrete graph pairs. -/
theorem concrete_l2_graph_pair_energy_add_le
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n ≤
      (2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
        (2 : ℝ) • concreteL2GraphPairEnergyTerm q n := by
  unfold concreteL2GraphPairEnergyTerm concreteL2GraphPairAdd
  have hfst := concrete_l2_r2_sq_add_le_two_sq_add_two_sq
    ((concreteL2GraphPairFst p).1 n) ((concreteL2GraphPairFst q).1 n)
  have hsnd := concrete_l2_r2_sq_add_le_two_sq_add_two_sq
    ((concreteL2GraphPairSnd p).1 n) ((concreteL2GraphPairSnd q).1 n)
  have hsum := add_le_add hfst hsnd
  simpa [concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealAdd,
    two_smul, add_assoc, add_left_comm, add_comm] using hsum

/-- Summability of the add-energy upper bound. -/
theorem concrete_l2_graph_pair_energy_add_bound_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ =>
      (2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
        (2 : ℝ) • concreteL2GraphPairEnergyTerm q n := by
  exact ((concrete_l2_graph_pair_energy_summable p).const_smul (2 : ℝ)).add
    ((concrete_l2_graph_pair_energy_summable q).const_smul (2 : ℝ))

/-- Scalar graph-pair energy is pointwise scaled by `c^2`. -/
theorem concrete_l2_graph_pair_energy_smul_eq
    (c : ℝ) (p : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) n =
      (c ^ 2) • concreteL2GraphPairEnergyTerm p n := by
  unfold concreteL2GraphPairEnergyTerm concreteL2GraphPairSmul
  simp [concreteL2GraphPairFst, concreteL2GraphPairSnd, concreteL2RealSmul]
  ring

/-- Summability of scalar graph-pair energy. -/
theorem concrete_l2_graph_pair_energy_smul_summable
    (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ => concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) n := by
  have hseq :
      (fun n : ℕ => concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) n) =
        (fun n : ℕ => (c ^ 2) • concreteL2GraphPairEnergyTerm p n) := by
    funext n
    exact concrete_l2_graph_pair_energy_smul_eq c p n
  rw [hseq]
  exact (concrete_l2_graph_pair_energy_summable p).const_smul (c ^ 2)

/-- R2l graph-pair energy surface.  This is a norm-like square-energy layer for
future graph-norm work, but it is not yet a graph-norm topology, density theorem,
or graph-norm core theorem. -/
structure ConcreteL2R2GraphPairEnergySurface where
  r2kReady : concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurfaceReady
  energyTerm : ConcreteL2GraphPairSpace → ℕ → ℝ
  energyNonneg : ∀ (p : ConcreteL2GraphPairSpace) (n : ℕ), 0 ≤ energyTerm p n
  energySummable : ∀ p : ConcreteL2GraphPairSpace, Summable fun n : ℕ => energyTerm p n
  zeroEnergy : ∀ n : ℕ, energyTerm concreteL2GraphPairZero n = 0
  addEnergyEstimate : ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    energyTerm (concreteL2GraphPairAdd p q) n ≤
      (2 : ℝ) • energyTerm p n + (2 : ℝ) • energyTerm q n
  smulEnergyLaw : ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (n : ℕ),
    energyTerm (concreteL2GraphPairSmul c p) n = (c ^ 2) • energyTerm p n
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2l graph-pair energy surface. -/
def concreteL2R2GraphPairEnergySurface : ConcreteL2R2GraphPairEnergySurface :=
  { r2kReady :=
      concrete_analytic_spine_l2_r2_diagonal_graph_linear_substructure_surface_ready
    energyTerm := concreteL2GraphPairEnergyTerm
    energyNonneg := concrete_l2_graph_pair_energy_term_nonneg
    energySummable := concrete_l2_graph_pair_energy_summable
    zeroEnergy := concrete_l2_graph_pair_energy_zero_ext
    addEnergyEstimate := concrete_l2_graph_pair_energy_add_le
    smulEnergyLaw := concrete_l2_graph_pair_energy_smul_eq
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2l readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurfaceReady ∧
  (∀ p : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ∧
  (∀ n : ℕ, concreteL2GraphPairEnergyTerm concreteL2GraphPairZero n = 0) ∧
  (∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairAdd p q) n ≤
      (2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
        (2 : ℝ) • concreteL2GraphPairEnergyTerm q n) ∧
  (∀ (c : ℝ) (p : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairEnergyTerm (concreteL2GraphPairSmul c p) n =
      (c ^ 2) • concreteL2GraphPairEnergyTerm p n) ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergySurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2l. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_diagonal_graph_linear_substructure_surface_ready <|
      And.intro concrete_l2_graph_pair_energy_summable <|
        And.intro concrete_l2_graph_pair_energy_zero_ext <|
          And.intro concrete_l2_graph_pair_energy_add_le <|
            And.intro concrete_l2_graph_pair_energy_smul_eq <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial trivial

/-- Boundary marker for R2l. -/
def concreteAnalyticSpineL2R2GraphPairEnergyHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergySurfaceReady

/-- Boundary theorem for R2l. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_surface_ready

end

end MathlibAnalytic
end MGAP4D
