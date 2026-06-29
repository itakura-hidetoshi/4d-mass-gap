import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsPairingAlgebra

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Each native local fluctuation projection is symmetric for the Gibbs
pairing. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_gibbsPairing_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathFluctuationLinearMap e g) := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_oriented_gibbsPairingReal_sub_left,
    finite_oriented_gibbsPairingReal_sub_right,
    finite_oriented_singleLinkHeatBathProjectionLinearMap_gibbsPairing_symm]

/-- Native observable heat-bath Hamiltonian `H_HB = sum_e Q_e`. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable
    (L : FiniteOrientedLatticeWilsonSystem) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) :=
  ∑ e : L.Edge, L.singleLinkHeatBathFluctuationLinearMap e

@[simp] theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathHamiltonianObservable f =
      ∑ e : L.Edge,
        L.singleLinkHeatBathFluctuationLinearMap e f := by
  classical
  simp [FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable]

/-- The native observable heat-bath Hamiltonian is Gibbs symmetric. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_gibbsPairing_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathHamiltonianObservable g) := by
  classical
  rw [finite_oriented_singleLinkHeatBathHamiltonianObservable_apply,
    finite_oriented_singleLinkHeatBathHamiltonianObservable_apply,
    finite_oriented_gibbsPairingReal_finset_sum_left,
    finite_oriented_gibbsPairingReal_finset_sum_right]
  apply Finset.sum_congr rfl
  intro e _he
  exact
    finite_oriented_singleLinkHeatBathFluctuationLinearMap_gibbsPairing_symm
      L e f g

/-- Pairing a local fluctuation with the original observable equals its own
weighted squared norm. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_fluctuation_left_eq_self
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f) f =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  calc
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f) f =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathProjectionLinearMap e f +
          L.singleLinkHeatBathFluctuationLinearMap e f) := by
      rw [finite_oriented_singleLinkHeatBath_projection_add_fluctuation]
    _ =
        L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuationLinearMap e f)
            (L.singleLinkHeatBathProjectionLinearMap e f) +
          L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuationLinearMap e f)
            (L.singleLinkHeatBathFluctuationLinearMap e f) :=
      finite_oriented_gibbsPairingReal_add_right L _ _ _
    _ = L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
      rw [finite_oriented_singleLinkHeatBath_gibbsPairing_fluctuation_projection_zero]
      simp

/-- The native observable Hamiltonian quadratic form is exactly the native
single-link heat-bath Dirichlet form. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_quadraticForm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f =
      L.singleLinkHeatBathDirichletForm f := by
  classical
  calc
    L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f =
      ∑ e : L.Edge,
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f) f := by
      rw [finite_oriented_singleLinkHeatBathHamiltonianObservable_apply,
        finite_oriented_gibbsPairingReal_finset_sum_left]
    _ = ∑ e : L.Edge,
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact
        finite_oriented_singleLinkHeatBath_gibbsPairing_fluctuation_left_eq_self
          L e f
    _ = L.singleLinkHeatBathDirichletForm f :=
      (finite_oriented_singleLinkHeatBathDirichletForm_eq_sum_gibbsPairing_fluctuation
        L f).symm

/-- The native observable heat-bath Hamiltonian is nonnegative in quadratic
form. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsPairingReal
      (L.singleLinkHeatBathHamiltonianObservable f) f := by
  rw [finite_oriented_singleLinkHeatBathHamiltonianObservable_quadraticForm]
  exact finite_oriented_singleLinkHeatBathDirichletForm_nonneg L f

/-- Every local fluctuation annihilates the constant-one observable. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    L.singleLinkHeatBathFluctuationLinearMap e
        (fun _ : L.Configuration => (1 : ℝ)) = 0 := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_oriented_singleLinkHeatBathProjectionLinearMap_apply,
    finite_oriented_singleLinkHeatBathProjection_one]
  simp

/-- The native observable heat-bath Hamiltonian has zero vacuum energy. -/
theorem finite_oriented_singleLinkHeatBathHamiltonianObservable_one
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.singleLinkHeatBathHamiltonianObservable
        (fun _ : L.Configuration => (1 : ℝ)) = 0 := by
  classical
  rw [finite_oriented_singleLinkHeatBathHamiltonianObservable_apply]
  apply Finset.sum_eq_zero
  intro e _he
  exact finite_oriented_singleLinkHeatBathFluctuationLinearMap_one L e

end

end MathlibAnalytic
end MGAP4D
