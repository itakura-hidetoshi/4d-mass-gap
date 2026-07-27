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

end

end MathlibAnalytic
end MGAP4D
