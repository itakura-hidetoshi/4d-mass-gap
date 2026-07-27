import MGAP4D.MathlibAnalytic.LinearMarkovDetailedBalancePairLaw
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTransitionExpectation
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Gibbs pairing is homogeneous in its first observable. -/
theorem finite_lattice_gibbsPairingReal_smul_left_randomScan
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (c • f) g =
      c * L.gibbsPairingReal f g := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Gibbs pairing is homogeneous in its second observable. -/
theorem finite_lattice_gibbsPairingReal_smul_right_randomScan
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f (c • g) =
      c * L.gibbsPairingReal f g := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Gibbs pairing commutes with a finite sum in its first observable. -/
theorem finite_lattice_gibbsPairingReal_sum_left_randomScan
    {ι : Type*} [Fintype ι]
    (L : FiniteLatticeWilsonSystem)
    (F : ι → L.Configuration → ℝ)
    (g : L.Configuration → ℝ) :
    L.gibbsPairingReal (fun A => ∑ i : ι, F i A) g =
      ∑ i : ι, L.gibbsPairingReal (F i) g := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Gibbs pairing commutes with a finite sum in its second observable. -/
theorem finite_lattice_gibbsPairingReal_sum_right_randomScan
    {ι : Type*} [Fintype ι]
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (G : ι → L.Configuration → ℝ) :
    L.gibbsPairingReal f (fun A => ∑ i : ι, G i A) =
      ∑ i : ι, L.gibbsPairingReal f (G i) := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The random-scan sweep is the normalized function-valued sum of the exact
single-link heat-bath projections. -/
theorem finite_lattice_randomScanHeatBathSweep_eq_smul_sum
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.randomScanHeatBathSweep f =
      (Fintype.card L.Edge : ℝ)⁻¹ •
        (fun A =>
          ∑ e : L.Edge, L.singleLinkHeatBathProjection e f A) := by
  funext A
  rfl

/-- Expand the Gibbs pairing with a random-scan sweep in the first slot as the
uniform average of the single-link Gibbs pairings. -/
theorem finite_lattice_gibbsPairingReal_randomScanHeatBathSweep_left
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.randomScanHeatBathSweep f) g =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g := by
  rw [finite_lattice_randomScanHeatBathSweep_eq_smul_sum]
  rw [finite_lattice_gibbsPairingReal_smul_left_randomScan]
  rw [finite_lattice_gibbsPairingReal_sum_left_randomScan]

/-- Expand the Gibbs pairing with a random-scan sweep in the second slot as the
uniform average of the single-link Gibbs pairings. -/
theorem finite_lattice_gibbsPairingReal_randomScanHeatBathSweep_right
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f (L.randomScanHeatBathSweep g) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  rw [finite_lattice_randomScanHeatBathSweep_eq_smul_sum]
  rw [finite_lattice_gibbsPairingReal_smul_right_randomScan]
  rw [finite_lattice_gibbsPairingReal_sum_right_randomScan]

/-- The normalized finite Wilson random-scan heat-bath sweep is symmetric for
the finite Gibbs pairing. -/
theorem finite_lattice_randomScanHeatBathSweep_gibbsPairing_symm
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.randomScanHeatBathSweep f) g =
      L.gibbsPairingReal f (L.randomScanHeatBathSweep g) := by
  rw [finite_lattice_gibbsPairingReal_randomScanHeatBathSweep_left,
    finite_lattice_gibbsPairingReal_randomScanHeatBathSweep_right]
  apply congrArg
    (fun r : ℝ => (Fintype.card L.Edge : ℝ)⁻¹ * r)
  apply Finset.sum_congr rfl
  intro e _he
  exact finite_lattice_singleLinkHeatBath_gibbsPairing_projection_symm
    L e f g

/-- Pairing against a point indicator in the second slot evaluates the first
observable at that point. -/
theorem finite_lattice_gibbsPairingReal_indicator_right
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) :
    L.gibbsPairingReal f
        (fun C => if C = A then (1 : ℝ) else 0) =
      L.gibbsProbabilityReal A * f A := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  simp [mul_assoc]

/-- Pairing a point indicator in the first slot evaluates the second observable
at that point. -/
theorem finite_lattice_gibbsPairingReal_indicator_left
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (fun C => if C = A then (1 : ℝ) else 0) g =
      L.gibbsProbabilityReal A * g A := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  simp [mul_assoc]

/-- Applying the random-scan sweep to a point indicator recovers the point mass
of the honest transition PMF. -/
theorem finite_lattice_randomScanHeatBathSweep_indicator
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (A B : L.Configuration) :
    L.randomScanHeatBathSweep
        (fun C => if C = B then (1 : ℝ) else 0) A =
      (L.randomScanTransitionPMF A B).toReal := by
  rw [← finite_lattice_randomScanTransitionPMF_expectation]
  unfold finitePMFExpectationReal
  simp

/-- Pointwise real detailed balance for the actual finite Wilson random-scan
transition PMF. -/
theorem finite_lattice_randomScanTransitionPMF_detailedBalance_real
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (A B : L.Configuration) :
    L.gibbsProbabilityReal A *
        (L.randomScanTransitionPMF A B).toReal =
      L.gibbsProbabilityReal B *
        (L.randomScanTransitionPMF B A).toReal := by
  have hsym :=
    finite_lattice_randomScanHeatBathSweep_gibbsPairing_symm
      L
      (fun C : L.Configuration => if C = B then (1 : ℝ) else 0)
      (fun C : L.Configuration => if C = A then (1 : ℝ) else 0)
  rw [finite_lattice_gibbsPairingReal_indicator_right,
    finite_lattice_gibbsPairingReal_indicator_left] at hsym
  rw [finite_lattice_randomScanHeatBathSweep_indicator,
    finite_lattice_randomScanHeatBathSweep_indicator] at hsym
  exact hsym

/-- The concrete finite Wilson random-scan transition satisfies the generic
finite-state detailed-balance predicate. -/
theorem finite_lattice_randomScanDetailedBalanceReal
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    LinearMarkovDetailedBalanceReal
      L.gibbsPMF L.randomScanTransitionPMF := by
  intro A B
  simpa [FiniteLatticeWilsonSystem.gibbsProbabilityReal] using
    finite_lattice_randomScanTransitionPMF_detailedBalance_real L A B

/-- The Gibbs-started one-step finite Wilson random-scan path law is exactly
invariant under time reversal. -/
theorem finite_lattice_randomScanPairPMF_map_swap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanPairPMF.map linearMarkovPairSwap =
      L.randomScanPairPMF := by
  unfold FiniteLatticeWilsonSystem.randomScanPairPMF
  exact linearMarkovPairPMF_map_swap_of_detailedBalanceReal
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L)

/-- Reflection invariance of the actual one-step random-scan path law in
expectation form. -/
theorem finite_lattice_randomScanPairPMF_expectation_swap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (H : L.Configuration × L.Configuration → ℝ) :
    finitePMFExpectationReal L.randomScanPairPMF
        (H ∘ linearMarkovPairSwap) =
      finitePMFExpectationReal L.randomScanPairPMF H :=
  linearMarkovPairPMF_expectation_swap_of_detailedBalanceReal
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) H

end

end MathlibAnalytic
end MGAP4D
