import MGAP4D.MathlibAnalytic.FinitePMFRealExpectation
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFiniteDimensionalPMF
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Expectation under the actual finite Wilson random-scan transition PMF is
exactly the previously constructed random-scan heat-bath observable operator. -/
theorem finite_lattice_randomScanTransitionPMF_expectation
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (A : L.Configuration)
    (f : L.Configuration → ℝ) :
    finitePMFExpectationReal (L.randomScanTransitionPMF A) f =
      L.randomScanHeatBathSweep f A := by
  classical
  unfold FiniteLatticeWilsonSystem.randomScanTransitionPMF
  rw [finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_map]
  rw [finite_lattice_randomScanHeatBathSweep_apply]
  unfold finitePMFExpectationReal
    FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
  simp [PMF.uniformOfFintype_apply, Finset.mul_sum]

/-- Finite-PMF expectation in the Wilson Gibbs PMF is the existing finite Gibbs
expectation functional. -/
@[simp] theorem finite_lattice_finitePMFExpectationReal_gibbsPMF
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    finitePMFExpectationReal L.gibbsPMF f =
      L.gibbsExpectationReal f := by
  classical
  unfold finitePMFExpectationReal
    FiniteLatticeWilsonSystem.gibbsExpectationReal
    FiniteLatticeWilsonSystem.gibbsProbabilityReal

/-- Gibbs expectation is homogeneous. -/
theorem finite_lattice_gibbsExpectationReal_smul
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ) (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal (c • f) =
      c * L.gibbsExpectationReal f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsExpectationReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Gibbs expectation commutes with finite sums of observables. -/
theorem finite_lattice_gibbsExpectationReal_sum
    {ι : Type*} [Fintype ι]
    (L : FiniteLatticeWilsonSystem)
    (F : ι → L.Configuration → ℝ) :
    L.gibbsExpectationReal (fun A => ∑ i : ι, F i A) =
      ∑ i : ι, L.gibbsExpectationReal (F i) := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsExpectationReal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Exact single-link Wilson heat-bath resampling preserves finite Gibbs
expectation. -/
theorem finite_lattice_gibbsExpectationReal_singleLinkHeatBathProjection
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal (L.singleLinkHeatBathProjection e f) =
      L.gibbsExpectationReal f := by
  classical
  have hsym :=
    finite_lattice_singleLinkHeatBath_gibbsPairing_projection_symm
      L e f (fun _ : L.Configuration => (1 : ℝ))
  have hone :
      L.singleLinkHeatBathProjection e
          (fun _ : L.Configuration => (1 : ℝ)) =
        fun _ => 1 := by
    apply finite_lattice_singleLinkHeatBathProjection_fixes
    intro A B _hAgree
    rfl
  rw [hone] at hsym
  simpa [FiniteLatticeWilsonSystem.gibbsPairingReal,
    FiniteLatticeWilsonSystem.gibbsExpectationReal] using hsym

/-- The normalized random-scan Wilson heat-bath sweep preserves finite Gibbs
expectation. -/
theorem finite_lattice_gibbsExpectationReal_randomScanHeatBathSweep
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal (L.randomScanHeatBathSweep f) =
      L.gibbsExpectationReal f := by
  classical
  have hcardNat : Fintype.card L.Edge ≠ 0 := Fintype.card_ne_zero
  have hcardReal : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hSweep :
      L.randomScanHeatBathSweep f =
        (Fintype.card L.Edge : ℝ)⁻¹ •
          (fun A =>
            ∑ e : L.Edge, L.singleLinkHeatBathProjection e f A) := by
    funext A
    simp [FiniteLatticeWilsonSystem.randomScanHeatBathSweep,
      FiniteLatticeWilsonSystem.singleLinkHeatBathOperator,
      FiniteLatticeWilsonSystem.singleLinkHeatBathProjection]
  rw [hSweep, finite_lattice_gibbsExpectationReal_smul,
    finite_lattice_gibbsExpectationReal_sum]
  simp_rw [finite_lattice_gibbsExpectationReal_singleLinkHeatBathProjection]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcardReal]

/-- The terminal-coordinate expectation of the Gibbs-started one-step path law
is again the Gibbs expectation. -/
theorem finite_lattice_randomScanPairPMF_snd_expectation
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (f : L.Configuration → ℝ) :
    finitePMFExpectationReal L.randomScanPairPMF
        (fun AB => f AB.2) =
      L.gibbsExpectationReal f := by
  unfold FiniteLatticeWilsonSystem.randomScanPairPMF
    linearMarkovPairPMF
  rw [finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_map]
  change finitePMFExpectationReal L.gibbsPMF
      (fun A =>
        finitePMFExpectationReal (L.randomScanTransitionPMF A) f) =
    L.gibbsExpectationReal f
  simp_rw [finite_lattice_randomScanTransitionPMF_expectation]
  rw [finite_lattice_finitePMFExpectationReal_gibbsPMF]
  exact finite_lattice_gibbsExpectationReal_randomScanHeatBathSweep L f

end

end MathlibAnalytic
end MGAP4D
