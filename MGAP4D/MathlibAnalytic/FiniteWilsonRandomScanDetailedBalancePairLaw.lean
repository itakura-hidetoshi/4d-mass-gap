import MGAP4D.MathlibAnalytic.LinearMarkovDetailedBalancePairLaw
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTransitionExpectation
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Expand the Gibbs pairing with a random-scan sweep in the first slot as the
uniform average of the single-link Gibbs pairings. -/
theorem finite_lattice_gibbsPairingReal_randomScanHeatBathSweep_left
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.randomScanHeatBathSweep f) g =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.randomScanHeatBathSweep
    FiniteLatticeWilsonSystem.singleLinkHeatBathOperator
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
  calc
    ∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          ((Fintype.card L.Edge : ℝ)⁻¹ *
            ∑ e : L.Edge,
              L.singleLinkConditionalExpectation f A e) * g A =
      ∑ A : L.Configuration, ∑ e : L.Edge,
        (Fintype.card L.Edge : ℝ)⁻¹ *
          (L.gibbsProbabilityReal A *
            L.singleLinkConditionalExpectation f A e * g A) := by
              apply Finset.sum_congr rfl
              intro A _hA
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _he
              ring
    _ = ∑ e : L.Edge, ∑ A : L.Configuration,
        (Fintype.card L.Edge : ℝ)⁻¹ *
          (L.gibbsProbabilityReal A *
            L.singleLinkConditionalExpectation f A e * g A) := by
              rw [Finset.sum_comm]
    _ = (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge, ∑ A : L.Configuration,
          L.gibbsProbabilityReal A *
            L.singleLinkConditionalExpectation f A e * g A := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _he
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro A _hA
              ring

/-- Expand the Gibbs pairing with a random-scan sweep in the second slot as the
uniform average of the single-link Gibbs pairings. -/
theorem finite_lattice_gibbsPairingReal_randomScanHeatBathSweep_right
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f (L.randomScanHeatBathSweep g) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.randomScanHeatBathSweep
    FiniteLatticeWilsonSystem.singleLinkHeatBathOperator
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
  calc
    ∑ A : L.Configuration,
        L.gibbsProbabilityReal A * f A *
          ((Fintype.card L.Edge : ℝ)⁻¹ *
            ∑ e : L.Edge,
              L.singleLinkConditionalExpectation g A e) =
      ∑ A : L.Configuration, ∑ e : L.Edge,
        (Fintype.card L.Edge : ℝ)⁻¹ *
          (L.gibbsProbabilityReal A * f A *
            L.singleLinkConditionalExpectation g A e) := by
              apply Finset.sum_congr rfl
              intro A _hA
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _he
              ring
    _ = ∑ e : L.Edge, ∑ A : L.Configuration,
        (Fintype.card L.Edge : ℝ)⁻¹ *
          (L.gibbsProbabilityReal A * f A *
            L.singleLinkConditionalExpectation g A e) := by
              rw [Finset.sum_comm]
    _ = (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge, ∑ A : L.Configuration,
          L.gibbsProbabilityReal A * f A *
            L.singleLinkConditionalExpectation g A e := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _he
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro A _hA
              ring

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
  classical
  have hsym :=
    finite_lattice_randomScanHeatBathSweep_gibbsPairing_symm
      L
      (fun C : L.Configuration => if C = B then (1 : ℝ) else 0)
      (fun C : L.Configuration => if C = A then (1 : ℝ) else 0)
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal at hsym
  simp_rw [← finite_lattice_randomScanTransitionPMF_expectation] at hsym
  unfold finitePMFExpectationReal at hsym
  simpa [mul_assoc] using hsym

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
