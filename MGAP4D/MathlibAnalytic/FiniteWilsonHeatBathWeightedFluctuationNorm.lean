import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPythagorean
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationEnergy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The constant-one observable is fixed by exact single-link conditional
expectation. -/
theorem finite_lattice_singleLinkHeatBathProjection_one
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    L.singleLinkHeatBathProjection e
        (fun _ : L.Configuration => (1 : ℝ)) =
      (fun _ : L.Configuration => (1 : ℝ)) := by
  apply finite_lattice_singleLinkHeatBathProjection_fixes
  intro A B _hAgree
  rfl

/-- Conditional fluctuation energy is conditional expectation of the squared
local fluctuation. -/
theorem finite_lattice_singleLinkConditionalFluctuationEnergy_eq_projection_sq
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkConditionalFluctuationEnergy f A e =
      L.singleLinkHeatBathProjection e
        (fun B : L.Configuration =>
          (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2) A := by
  classical
  rfl

/-- Gibbs averaging removes one exact heat-bath conditional expectation.  In
particular, averaged local fluctuation energy is the Gibbs pairing of `Q_e f`
with itself. -/
theorem finite_lattice_averagedSingleLinkFluctuationEnergy_eq_gibbsPairing
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) (e : L.Edge) :
    L.averagedSingleLinkFluctuationEnergy f e =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  have hSymm :=
    finite_lattice_singleLinkHeatBath_gibbsPairing_projection_symm
      L e
      (fun B : L.Configuration =>
        (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2)
      (fun _ : L.Configuration => (1 : ℝ))
  rw [finite_lattice_singleLinkHeatBathProjection_one] at hSymm
  calc
    L.averagedSingleLinkFluctuationEnergy f e =
        L.gibbsPairingReal
          (L.singleLinkHeatBathProjection e
            (fun B : L.Configuration =>
              (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2))
          (fun _ : L.Configuration => (1 : ℝ)) := by
      classical
      unfold FiniteLatticeWilsonSystem.averagedSingleLinkFluctuationEnergy
      unfold FiniteLatticeWilsonSystem.gibbsPairingReal
      apply Finset.sum_congr rfl
      intro A _hA
      rw [finite_lattice_singleLinkConditionalFluctuationEnergy_eq_projection_sq]
      ring
    _ = L.gibbsPairingReal
          (fun B : L.Configuration =>
            (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2)
          (fun _ : L.Configuration => (1 : ℝ)) := hSymm
    _ = L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
      classical
      unfold FiniteLatticeWilsonSystem.gibbsPairingReal
      apply Finset.sum_congr rfl
      intro A _hA
      ring

/-- The Gibbs average of the exact single-link conditional variance is the
weighted squared norm of the complementary projection `Q_e`. -/
theorem finite_lattice_averagedSingleLinkVariance_eq_gibbsPairing_fluctuation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) (e : L.Edge) :
    L.averagedSingleLinkVariance f e =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  rw [finite_lattice_averagedSingleLinkVariance_eq_fluctuationEnergy,
    finite_lattice_averagedSingleLinkFluctuationEnergy_eq_gibbsPairing]

/-- The full finite Wilson heat-bath Dirichlet form is the sum of the weighted
squared norms of all local fluctuation projections. -/
theorem finite_lattice_singleLinkHeatBathDirichletForm_eq_sum_gibbsPairing_fluctuation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm f =
      ∑ e : L.Edge,
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  rw [finite_lattice_singleLinkHeatBathDirichletForm_eq_fluctuationEnergy]
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathFluctuationDirichletForm
  apply Finset.sum_congr rfl
  intro e _he
  rw [finite_lattice_averagedSingleLinkFluctuationEnergy_eq_gibbsPairing]

end

end MathlibAnalytic
end MGAP4D
