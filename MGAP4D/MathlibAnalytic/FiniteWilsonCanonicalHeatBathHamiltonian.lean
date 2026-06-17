import MGAP4D.MathlibAnalytic.FiniteWilsonConcreteGibbsHilbertHamiltonianBridge
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathWeightedFluctuationNorm

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Gibbs pairing is compatible with subtraction in its first argument. -/
theorem finite_lattice_gibbsPairingReal_sub_left
    (L : FiniteLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal (f - g) h =
      L.gibbsPairingReal f h - L.gibbsPairingReal g h := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.sub_apply]
  ring

/-- Gibbs pairing is compatible with subtraction in its second argument. -/
theorem finite_lattice_gibbsPairingReal_sub_right
    (L : FiniteLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal f (g - h) =
      L.gibbsPairingReal f g - L.gibbsPairingReal f h := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.sub_apply]
  ring

/-- Gibbs pairing commutes with a finite sum in its first argument. -/
theorem finite_lattice_gibbsPairingReal_finset_sum_left
    (L : FiniteLatticeWilsonSystem)
    {ι : Type*} (s : Finset ι)
    (F : ι → L.Configuration → ℝ)
    (g : L.Configuration → ℝ) :
    L.gibbsPairingReal (s.sum F) g =
      s.sum (fun i => L.gibbsPairingReal (F i) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [FiniteLatticeWilsonSystem.gibbsPairingReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,
        finite_lattice_gibbsPairingReal_add_left,
        ih,
        Finset.sum_insert ha]

/-- Gibbs pairing commutes with a finite sum in its second argument. -/
theorem finite_lattice_gibbsPairingReal_finset_sum_right
    (L : FiniteLatticeWilsonSystem)
    {ι : Type*} (s : Finset ι)
    (f : L.Configuration → ℝ)
    (G : ι → L.Configuration → ℝ) :
    L.gibbsPairingReal f (s.sum G) =
      s.sum (fun i => L.gibbsPairingReal f (G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [FiniteLatticeWilsonSystem.gibbsPairingReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,
        finite_lattice_gibbsPairingReal_add_right,
        ih,
        Finset.sum_insert ha]

/-- The local fluctuation projection `Q_e = I - P_e` is symmetric for the
finite Wilson Gibbs pairing. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_gibbsPairing_symm
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathFluctuationLinearMap e g) := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_lattice_gibbsPairingReal_sub_left,
    finite_lattice_gibbsPairingReal_sub_right,
    finite_lattice_singleLinkHeatBathProjectionLinearMap_gibbsPairing_symm]

/-- The observable heat-bath Hamiltonian is the sum of all local fluctuation
projections `Q_e`. -/
noncomputable def FiniteLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable
    (L : FiniteLatticeWilsonSystem) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) :=
  ∑ e : L.Edge, L.singleLinkHeatBathFluctuationLinearMap e

@[simp] theorem finite_lattice_singleLinkHeatBathHamiltonianObservable_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathHamiltonianObservable f =
      ∑ e : L.Edge,
        L.singleLinkHeatBathFluctuationLinearMap e f := by
  classical
  simp [FiniteLatticeWilsonSystem.singleLinkHeatBathHamiltonianObservable]

/-- The observable heat-bath Hamiltonian is symmetric for the Gibbs pairing. -/
theorem finite_lattice_singleLinkHeatBathHamiltonianObservable_gibbsPairing_symm
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathHamiltonianObservable g) := by
  classical
  rw [finite_lattice_singleLinkHeatBathHamiltonianObservable_apply,
    finite_lattice_singleLinkHeatBathHamiltonianObservable_apply,
    finite_lattice_gibbsPairingReal_finset_sum_left,
    finite_lattice_gibbsPairingReal_finset_sum_right]
  apply Finset.sum_congr rfl
  intro e _he
  exact
    finite_lattice_singleLinkHeatBathFluctuationLinearMap_gibbsPairing_symm
      L e f g

/-- A local fluctuation paired with the original observable equals its own
Gibbs squared norm. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_fluctuation_left_eq_self
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
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
      rw [finite_lattice_singleLinkHeatBath_projection_add_fluctuation]
    _ =
      L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathProjectionLinearMap e f) +
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) :=
      finite_lattice_gibbsPairingReal_add_right L _ _ _
    _ = L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) := by
      rw [finite_lattice_singleLinkHeatBath_gibbsPairing_fluctuation_projection_zero]
      simp

/-- The observable heat-bath Hamiltonian quadratic form is exactly the full
single-link heat-bath Dirichlet form. -/
theorem finite_lattice_singleLinkHeatBathHamiltonianObservable_quadraticForm
    (L : FiniteLatticeWilsonSystem)
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
      rw [finite_lattice_singleLinkHeatBathHamiltonianObservable_apply,
        finite_lattice_gibbsPairingReal_finset_sum_left]
    _ = ∑ e : L.Edge,
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact
        finite_lattice_singleLinkHeatBath_gibbsPairing_fluctuation_left_eq_self
          L e f
    _ = L.singleLinkHeatBathDirichletForm f :=
      (finite_lattice_singleLinkHeatBathDirichletForm_eq_sum_gibbsPairing_fluctuation
        L f).symm

/-- Transport the observable heat-bath Hamiltonian through the square-root
Gibbs-density linear equivalence to the concrete Gibbs Hilbert carrier. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsHeatBathHamiltonianLinearMap
    (L : FiniteLatticeWilsonSystem) :
    L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace :=
  L.gibbsHilbertEmbedLinearMap.comp
    (L.singleLinkHeatBathHamiltonianObservable.comp
      L.gibbsHilbertObserveLinearMap)

@[simp] theorem finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsHeatBathHamiltonianLinearMap x =
      L.gibbsHilbertEmbedLinearMap
        (L.singleLinkHeatBathHamiltonianObservable
          (L.gibbsHilbertObserveLinearMap x)) :=
  rfl

/-- The canonical Gibbs Hilbert heat-bath Hamiltonian is symmetric. -/
theorem finite_lattice_gibbsHeatBathHamiltonianLinearMap_isSymmetric
    (L : FiniteLatticeWilsonSystem) :
    L.gibbsHeatBathHamiltonianLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) y =
        inner ℝ
          (L.gibbsHilbertEmbedLinearMap
            (L.singleLinkHeatBathHamiltonianObservable
              (L.gibbsHilbertObserveLinearMap x)))
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap y)) := by
      rw [finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply,
        finite_lattice_gibbsHilbert_embed_observe]
    _ = L.gibbsPairingReal
          (L.singleLinkHeatBathHamiltonianObservable
            (L.gibbsHilbertObserveLinearMap x))
          (L.gibbsHilbertObserveLinearMap y) :=
      finite_lattice_gibbsHilbert_inner_embed L _ _
    _ = L.gibbsPairingReal
          (L.gibbsHilbertObserveLinearMap x)
          (L.singleLinkHeatBathHamiltonianObservable
            (L.gibbsHilbertObserveLinearMap y)) :=
      finite_lattice_singleLinkHeatBathHamiltonianObservable_gibbsPairing_symm
        L _ _
    _ = inner ℝ
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x))
          (L.gibbsHilbertEmbedLinearMap
            (L.singleLinkHeatBathHamiltonianObservable
              (L.gibbsHilbertObserveLinearMap y))) :=
      (finite_lattice_gibbsHilbert_inner_embed L _ _).symm
    _ = inner ℝ x (L.gibbsHeatBathHamiltonianLinearMap y) := by
      rw [finite_lattice_gibbsHilbert_embed_observe,
        finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply]

/-- Every local fluctuation annihilates the constant-one observable. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_one
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    L.singleLinkHeatBathFluctuationLinearMap e
        (fun _ : L.Configuration => (1 : ℝ)) = 0 := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_lattice_singleLinkHeatBathProjectionLinearMap_apply,
    finite_lattice_singleLinkHeatBathProjection_one]
  simp

/-- The observable heat-bath Hamiltonian annihilates the constant-one
observable. -/
theorem finite_lattice_singleLinkHeatBathHamiltonianObservable_one
    (L : FiniteLatticeWilsonSystem) :
    L.singleLinkHeatBathHamiltonianObservable
        (fun _ : L.Configuration => (1 : ℝ)) = 0 := by
  classical
  rw [finite_lattice_singleLinkHeatBathHamiltonianObservable_apply]
  apply Finset.sum_eq_zero
  intro e _he
  exact finite_lattice_singleLinkHeatBathFluctuationLinearMap_one L e

/-- The canonical heat-bath Hamiltonian has zero vacuum energy. -/
theorem finite_lattice_gibbsHeatBathHamiltonianLinearMap_vacuum
    (L : FiniteLatticeWilsonSystem) :
    L.gibbsHeatBathHamiltonianLinearMap L.gibbsHilbertVacuum = 0 := by
  rw [finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply,
    FiniteLatticeWilsonSystem.gibbsHilbertVacuum,
    finite_lattice_gibbsHilbert_observe_embed,
    finite_lattice_singleLinkHeatBathHamiltonianObservable_one]
  simp

/-- The canonical Gibbs Hilbert Hamiltonian quadratic form is exactly the
single-link heat-bath Dirichlet form of the recovered observable. -/
theorem finite_lattice_gibbsHeatBathHamiltonianLinearMap_quadraticForm
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x =
      L.singleLinkHeatBathDirichletForm
        (L.gibbsHilbertObserveLinearMap x) := by
  calc
    inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x =
        inner ℝ
          (L.gibbsHilbertEmbedLinearMap
            (L.singleLinkHeatBathHamiltonianObservable
              (L.gibbsHilbertObserveLinearMap x)))
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x)) := by
      rw [finite_lattice_gibbsHeatBathHamiltonianLinearMap_apply,
        finite_lattice_gibbsHilbert_embed_observe]
    _ = L.gibbsPairingReal
          (L.singleLinkHeatBathHamiltonianObservable
            (L.gibbsHilbertObserveLinearMap x))
          (L.gibbsHilbertObserveLinearMap x) :=
      finite_lattice_gibbsHilbert_inner_embed L _ _
    _ = L.singleLinkHeatBathDirichletForm
          (L.gibbsHilbertObserveLinearMap x) :=
      finite_lattice_singleLinkHeatBathHamiltonianObservable_quadraticForm
        L _

/-- Build the complete concrete Hamiltonian bridge from the exact finite Wilson
heat-bath Poincare inequality alone. -/
noncomputable def finiteWilsonCanonicalHeatBathHamiltonianBridgeData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (hGap : (W.system i).ExactGapSingleLinkHeatBathPoincare) :
    FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData W i :=
  { hamiltonian := fun _n =>
      (W.system i).gibbsHeatBathHamiltonianLinearMap
    hamiltonianSymmetric := fun _n =>
      finite_lattice_gibbsHeatBathHamiltonianLinearMap_isSymmetric
        (W.system i)
    vacuumEnergyZero := fun _n =>
      finite_lattice_gibbsHeatBathHamiltonianLinearMap_vacuum
        (W.system i)
    hamiltonianQuadraticForm_eq_heatBathDirichlet := fun _n x =>
      finite_lattice_gibbsHeatBathHamiltonianLinearMap_quadraticForm
        (W.system i) x
    exactGapSingleLinkHeatBathPoincare := hGap
    ExcitedDimension :=
      Module.finrank ℝ
        (finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum)
    excitedFinrank := rfl }

/-- The exact finite Wilson heat-bath Poincare inequality now yields the
vacuum-centered canonical Hamiltonian lower bound without any additional
Hamiltonian construction hypothesis. -/
theorem finite_wilson_exact_heat_bath_poincare_implies_canonical_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (hGap : (W.system i).ExactGapSingleLinkHeatBathPoincare)
    (x : (W.system i).GibbsHilbertSpace) :
    exactGapValueReal *
        ‖finiteVacuumCentered (W.system i).gibbsHilbertVacuum x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsHeatBathHamiltonianLinearMap x) x :=
  finite_wilson_concrete_gibbs_hilbert_implies_vacuum_poincare
    (finiteWilsonCanonicalHeatBathHamiltonianBridgeData W i hGap) 0 x

end

end MathlibAnalytic
end MGAP4D
