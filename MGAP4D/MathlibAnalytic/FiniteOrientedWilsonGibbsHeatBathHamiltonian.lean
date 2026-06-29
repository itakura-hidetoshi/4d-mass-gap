import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsHilbertEquivalence
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonCanonicalHeatBathHamiltonianObservable

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Native oriented heat-bath Hamiltonian transported through the square-root
Gibbs-density linear equivalence. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsHeatBathHamiltonianLinearMap
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.GibbsHilbertSpace →ₗ[ℝ] L.GibbsHilbertSpace :=
  L.gibbsHilbertEmbedLinearMap.comp
    (L.singleLinkHeatBathHamiltonianObservable.comp
      L.gibbsHilbertObserveLinearMap)

@[simp] theorem finite_oriented_gibbsHeatBathHamiltonianLinearMap_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsHeatBathHamiltonianLinearMap x =
      L.gibbsHilbertEmbedLinearMap
        (L.singleLinkHeatBathHamiltonianObservable
          (L.gibbsHilbertObserveLinearMap x)) :=
  rfl

/-- The native oriented Gibbs Hilbert heat-bath Hamiltonian is symmetric. -/
theorem finite_oriented_gibbsHeatBathHamiltonianLinearMap_isSymmetric
    (L : FiniteOrientedLatticeWilsonSystem) :
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
      rw [finite_oriented_gibbsHeatBathHamiltonianLinearMap_apply,
        finite_oriented_gibbsHilbert_embed_observe]
    _ = L.gibbsPairingReal
          (L.singleLinkHeatBathHamiltonianObservable
            (L.gibbsHilbertObserveLinearMap x))
          (L.gibbsHilbertObserveLinearMap y) :=
      finite_oriented_gibbsHilbert_inner_embed L _ _
    _ = L.gibbsPairingReal
          (L.gibbsHilbertObserveLinearMap x)
          (L.singleLinkHeatBathHamiltonianObservable
            (L.gibbsHilbertObserveLinearMap y)) :=
      finite_oriented_singleLinkHeatBathHamiltonianObservable_gibbsPairing_symm
        L _ _
    _ = inner ℝ
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x))
          (L.gibbsHilbertEmbedLinearMap
            (L.singleLinkHeatBathHamiltonianObservable
              (L.gibbsHilbertObserveLinearMap y))) :=
      (finite_oriented_gibbsHilbert_inner_embed L _ _).symm
    _ = inner ℝ x (L.gibbsHeatBathHamiltonianLinearMap y) := by
      rw [finite_oriented_gibbsHilbert_embed_observe,
        finite_oriented_gibbsHeatBathHamiltonianLinearMap_apply]

/-- The native oriented heat-bath Hamiltonian has zero vacuum energy. -/
theorem finite_oriented_gibbsHeatBathHamiltonianLinearMap_vacuum
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.gibbsHeatBathHamiltonianLinearMap L.gibbsHilbertVacuum = 0 := by
  rw [finite_oriented_gibbsHeatBathHamiltonianLinearMap_apply,
    FiniteOrientedLatticeWilsonSystem.gibbsHilbertVacuum,
    finite_oriented_gibbsHilbert_observe_embed,
    finite_oriented_singleLinkHeatBathHamiltonianObservable_one]
  simp

/-- The native Gibbs Hilbert Hamiltonian quadratic form is exactly the native
single-link heat-bath Dirichlet form of the recovered observable. -/
theorem finite_oriented_gibbsHeatBathHamiltonianLinearMap_quadraticForm
    (L : FiniteOrientedLatticeWilsonSystem)
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
      rw [finite_oriented_gibbsHeatBathHamiltonianLinearMap_apply,
        finite_oriented_gibbsHilbert_embed_observe]
    _ = L.gibbsPairingReal
          (L.singleLinkHeatBathHamiltonianObservable
            (L.gibbsHilbertObserveLinearMap x))
          (L.gibbsHilbertObserveLinearMap x) :=
      finite_oriented_gibbsHilbert_inner_embed L _ _
    _ = L.singleLinkHeatBathDirichletForm
          (L.gibbsHilbertObserveLinearMap x) :=
      finite_oriented_singleLinkHeatBathHamiltonianObservable_quadraticForm
        L _

/-- The native Gibbs Hilbert heat-bath Hamiltonian is nonnegative. -/
theorem finite_oriented_gibbsHeatBathHamiltonianLinearMap_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    0 ≤ inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x := by
  rw [finite_oriented_gibbsHeatBathHamiltonianLinearMap_quadraticForm]
  exact finite_oriented_singleLinkHeatBathDirichletForm_nonneg
    L (L.gibbsHilbertObserveLinearMap x)

end

end MathlibAnalytic
end MGAP4D
