import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsHeatBathHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Package the native oriented finite heat-bath Hamiltonian using only its
native exact-gap Poincare inequality. -/
noncomputable def finiteOrientedWilsonNativeHeatBathHamiltonianGapData
    (L : FiniteOrientedLatticeWilsonSystem)
    (hGap : L.ExactGapSingleLinkHeatBathPoincare) :
    FiniteWilsonVacuumPoincareHamiltonianGapData :=
  { StateSpace := L.GibbsHilbertSpace
    stateNormedAddCommGroup := inferInstance
    stateInnerProductSpace := inferInstance
    stateFiniteDimensional := inferInstance
    vacuum := L.gibbsHilbertVacuum
    vacuum_norm := finite_oriented_gibbsHilbertVacuum_norm L
    hamiltonian := fun _n => L.gibbsHeatBathHamiltonianLinearMap
    hamiltonianSymmetric := fun _n =>
      finite_oriented_gibbsHeatBathHamiltonianLinearMap_isSymmetric L
    vacuumEnergyZero := fun _n =>
      finite_oriented_gibbsHeatBathHamiltonianLinearMap_vacuum L
    dirichletForm := fun _n x =>
      L.singleLinkHeatBathDirichletForm
        (L.gibbsHilbertObserveLinearMap x)
    hamiltonianQuadraticForm_eq_dirichletForm := fun _n x =>
      finite_oriented_gibbsHeatBathHamiltonianLinearMap_quadraticForm L x
    vacuumPoincareInequality := by
      intro _n x
      calc
        exactGapValueReal *
            ‖finiteVacuumCentered L.gibbsHilbertVacuum x‖ ^ 2 =
          exactGapValueReal *
            L.gibbsVarianceReal
              (L.gibbsHilbertObserveLinearMap x) := by
                rw [finite_oriented_gibbsHilbert_vacuumCentered_norm_sq_observe]
        _ ≤ L.singleLinkHeatBathDirichletForm
              (L.gibbsHilbertObserveLinearMap x) :=
          hGap (L.gibbsHilbertObserveLinearMap x)
    ExcitedDimension :=
      Module.finrank ℝ
        (finiteVacuumOrthogonal L.gibbsHilbertVacuum)
    excitedFinrank := rfl }

/-- Native oriented exact-gap Poincare implies the Hamiltonian lower bound on
the vacuum-orthogonal excitation sector. -/
theorem finite_oriented_native_hamiltonian_gap_on_vacuumOrthogonal
    (L : FiniteOrientedLatticeWilsonSystem)
    (hGap : L.ExactGapSingleLinkHeatBathPoincare)
    (x : L.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal L.gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (L.gibbsHeatBathHamiltonianLinearMap x) x :=
  finite_wilson_vacuum_poincare_implies_orthogonal_coercivity
    (finiteOrientedWilsonNativeHeatBathHamiltonianGapData L hGap)
    0 x hx

/-- Every eigenvalue of the native oriented Hamiltonian restricted to the
vacuum-orthogonal sector is bounded below by the public exact gap. -/
theorem finite_oriented_native_restricted_eigenvalues_ge_exactGap
    (L : FiniteOrientedLatticeWilsonSystem)
    (hGap : L.ExactGapSingleLinkHeatBathPoincare)
    (i : Fin
      (finiteOrientedWilsonNativeHeatBathHamiltonianGapData
        L hGap).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (finiteOrientedWilsonNativeHeatBathHamiltonianGapData
          L hGap).toDerivedInvarianceGapData.toVacuumOrthogonalGapData
        0).eigenvalues
          (finiteOrientedWilsonNativeHeatBathHamiltonianGapData
            L hGap).excitedFinrank
          i :=
  finite_wilson_vacuum_poincare_restricted_eigenvalues_ge_exactGap
    (finiteOrientedWilsonNativeHeatBathHamiltonianGapData L hGap)
    0 i

end

end MathlibAnalytic
end MGAP4D
