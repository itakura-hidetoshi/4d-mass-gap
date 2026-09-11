import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathFluctuationEnergy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The constant-one observable is fixed by native one-link conditional
expectation. -/
theorem finite_oriented_singleLinkHeatBathProjection_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    L.singleLinkHeatBathProjection e
        (fun _ : L.Configuration => (1 : ℝ)) =
      (fun _ : L.Configuration => (1 : ℝ)) := by
  apply finite_oriented_singleLinkHeatBathProjection_fixes
  intro A B _hAgree
  rfl

/-- Conditional fluctuation energy is conditional expectation of squared
native local fluctuation. -/
theorem finite_oriented_singleLinkConditionalFluctuationEnergy_eq_projection_sq
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.singleLinkConditionalFluctuationEnergy f A e =
      L.singleLinkHeatBathProjection e
        (fun B : L.Configuration =>
          (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2) A := by
  classical
  rfl

/-- Gibbs averaging removes one native conditional expectation, identifying
averaged fluctuation energy with the weighted squared norm of `Q_e f`. -/
theorem finite_oriented_averagedSingleLinkFluctuationEnergy_eq_gibbsPairing
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.averagedSingleLinkFluctuationEnergy f e =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  have hSymm :=
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
      L e
      (fun B : L.Configuration =>
        (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2)
      (fun _ : L.Configuration => (1 : ℝ))
  rw [finite_oriented_singleLinkHeatBathProjection_one] at hSymm
  calc
    L.averagedSingleLinkFluctuationEnergy f e =
        L.gibbsPairingReal
          (L.singleLinkHeatBathProjection e
            (fun B : L.Configuration =>
              (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2))
          (fun _ : L.Configuration => (1 : ℝ)) := by
      classical
      unfold
        FiniteOrientedLatticeWilsonSystem.averagedSingleLinkFluctuationEnergy
        FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
      apply Finset.sum_congr rfl
      intro A _hA
      rw [finite_oriented_singleLinkConditionalFluctuationEnergy_eq_projection_sq]
      ring
    _ = L.gibbsPairingReal
          (fun B : L.Configuration =>
            (L.singleLinkHeatBathFluctuationLinearMap e f B) ^ 2)
          (fun _ : L.Configuration => (1 : ℝ)) := hSymm
    _ = L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
      classical
      unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
      apply Finset.sum_congr rfl
      intro A _hA
      ring

/-- Averaged native conditional variance is the weighted squared norm of
`Q_e f`. -/
theorem finite_oriented_averagedSingleLinkVariance_eq_gibbsPairing_fluctuation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.averagedSingleLinkVariance f e =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  rw [finite_oriented_averagedSingleLinkVariance_eq_fluctuationEnergy,
    finite_oriented_averagedSingleLinkFluctuationEnergy_eq_gibbsPairing]

/-- The native heat-bath Dirichlet form is the sum of all weighted local
fluctuation squared norms. -/
theorem finite_oriented_singleLinkHeatBathDirichletForm_eq_sum_gibbsPairing_fluctuation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm f =
      ∑ e : L.Edge,
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  rw [finite_oriented_singleLinkHeatBathDirichletForm_eq_fluctuationEnergy]
  unfold
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuationDirichletForm
  apply Finset.sum_congr rfl
  intro e _he
  rw [finite_oriented_averagedSingleLinkFluctuationEnergy_eq_gibbsPairing]

end

end MathlibAnalytic
end MGAP4D
