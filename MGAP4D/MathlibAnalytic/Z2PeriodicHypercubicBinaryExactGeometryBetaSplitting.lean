import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryParameterLatticeExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

namespace Z2PeriodicHypercubicPlaquetteTrajectory

/-- Rebuild one periodic finite lattice at a supplied nonnegative coupling while
keeping the lattice size and selected plaquette fixed. -/
noncomputable def systemAtBeta
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) (beta : ℝ) (hBeta : 0 ≤ beta) :
    FiniteOrientedLatticeWilsonSystem := by
  have hPos : 0 < T.sideLength k :=
    lt_of_lt_of_le (by norm_num) (T.sideLength_ge_two k)
  letI : NeZero (T.sideLength k) := ⟨Nat.ne_of_gt hPos⟩
  exact z2PeriodicHypercubicOrientedWilsonSystem
    (T.sideLength k) beta hBeta

/-- The selected plaquette energy observable on the same lattice at a supplied
coupling. -/
noncomputable def plaquetteObservableAtBeta
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) (beta : ℝ) (hBeta : 0 ≤ beta) :
    (T.systemAtBeta k beta hBeta).Configuration → ℝ := by
  have hPos : 0 < T.sideLength k :=
    lt_of_lt_of_le (by norm_num) (T.sideLength_ge_two k)
  letI : NeZero (T.sideLength k) := ⟨Nat.ne_of_gt hPos⟩
  exact z2PeriodicHypercubicPlaquetteEnergyObservable
    (T.sideLength k) beta hBeta (T.plaquette k)

/-- Finite-volume Gibbs expectation of the selected plaquette at an arbitrary
nonnegative coupling on one fixed trajectory lattice. -/
noncomputable def plaquetteExpectationAtBeta
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) (beta : ℝ) (hBeta : 0 ≤ beta) : ℝ :=
  ∫ A : (T.systemAtBeta k beta hBeta).Configuration,
    T.plaquetteObservableAtBeta k beta hBeta A
    ∂((T.systemAtBeta k beta hBeta).gibbsProbabilityMeasure :
      Measure (T.systemAtBeta k beta hBeta).Configuration)

/-- At the trajectory coupling, the parametrized expectation is definitionally
the original finite-volume plaquette expectation. -/
theorem plaquetteExpectationAtBeta_trajectoryBeta
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) :
    T.plaquetteExpectationAtBeta k (T.beta k) (T.beta_nonneg k) =
      ∫ A : (T.system k).Configuration,
        T.plaquetteObservable k A
        ∂((T.system k).gibbsProbabilityMeasure :
          Measure (T.system k).Configuration) := by
  unfold plaquetteExpectationAtBeta plaquetteObservableAtBeta systemAtBeta
    Z2PeriodicHypercubicPlaquetteTrajectory.system
    Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteObservable
  rfl

end Z2PeriodicHypercubicPlaquetteTrajectory

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- The embedded Bernoulli coordinate equals the parametrized finite-volume
plaquette expectation evaluated at the trajectory coupling. -/
theorem embeddedBernoulliParameter_eq_plaquetteExpectationAtBeta
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    D.embeddedBernoulliParameter k =
      D.trajectory.plaquetteExpectationAtBeta k
        (D.trajectory.beta k) (D.trajectory.beta_nonneg k) := by
  rw [D.embeddedBernoulliParameter_eq_latticePlaquetteExpectation]
  exact (D.trajectory.plaquetteExpectationAtBeta_trajectoryBeta k).symm

/-- Coupling-response part of the inter-scale plaquette expectation increment:
change the coupling on the next lattice while keeping that lattice fixed. -/
noncomputable def couplingResponseIncrement
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) : ℝ :=
  D.trajectory.plaquetteExpectationAtBeta (k + 1)
      (D.trajectory.beta (k + 1)) (D.trajectory.beta_nonneg (k + 1)) -
    D.trajectory.plaquetteExpectationAtBeta (k + 1)
      (D.trajectory.beta k) (D.trajectory.beta_nonneg k)

/-- Geometry-response part of the inter-scale plaquette expectation increment:
change the lattice while keeping the earlier coupling fixed. -/
noncomputable def geometryResponseIncrement
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) : ℝ :=
  D.trajectory.plaquetteExpectationAtBeta (k + 1)
      (D.trajectory.beta k) (D.trajectory.beta_nonneg k) -
    D.trajectory.plaquetteExpectationAtBeta k
      (D.trajectory.beta k) (D.trajectory.beta_nonneg k)

/-- Exact algebraic splitting of each Bernoulli increment into coupling response
on the next fixed lattice and finite-volume geometry response at fixed coupling. -/
theorem embeddedBernoulliParameter_increment_eq_coupling_add_geometry
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    D.embeddedBernoulliParameter (k + 1) -
        D.embeddedBernoulliParameter k =
      D.couplingResponseIncrement k + D.geometryResponseIncrement k := by
  rw [D.embeddedBernoulliParameter_eq_plaquetteExpectationAtBeta,
    D.embeddedBernoulliParameter_eq_plaquetteExpectationAtBeta]
  unfold couplingResponseIncrement geometryResponseIncrement
  ring

/-- Therefore the absolute inter-scale increment is bounded by the sum of the
absolute coupling-response and geometry-response increments. -/
theorem abs_embeddedBernoulliParameter_increment_le_responses
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) :
    |D.embeddedBernoulliParameter (k + 1) -
        D.embeddedBernoulliParameter k| ≤
      |D.couplingResponseIncrement k| + |D.geometryResponseIncrement k| := by
  rw [D.embeddedBernoulliParameter_increment_eq_coupling_add_geometry]
  exact abs_add_le _ _

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
