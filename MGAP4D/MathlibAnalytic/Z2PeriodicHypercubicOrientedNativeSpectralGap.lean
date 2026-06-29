import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedNativeHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Complete finite-dimensional vacuum-orthogonal gap package for the native
periodic oriented `Z₂` Hamiltonian under the explicit small-coupling bound. -/
noncomputable def
    z2PeriodicHypercubicOrientedNativeScaledHamiltonianGapData
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let C := z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
    n hn beta hBeta hBetaLt
  { StateSpace := L.GibbsHilbertSpace
    stateNormedAddCommGroup := inferInstance
    stateInnerProductSpace := inferInstance
    stateFiniteDimensional := inferInstance
    vacuum := L.gibbsHilbertVacuum
    vacuum_norm := finite_oriented_gibbsHilbertVacuum_norm L
    hamiltonian := fun _k =>
      L.gibbsDobrushinScaledHeatBathHamiltonianLinearMap C
    hamiltonianSymmetric := fun _k =>
      finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_isSymmetric
        L C
    vacuumEnergyZero := fun _k =>
      finite_oriented_gibbsDobrushinScaledHeatBathHamiltonianLinearMap_vacuum
        L C
    hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal := by
      intro _k x hx
      exact
        finite_oriented_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
          L z2Gauge_inv_eq_self C x hx
    ExcitedDimension :=
      Module.finrank ℝ (finiteVacuumOrthogonal L.gibbsHilbertVacuum)
    excitedFinrank := rfl }

/-- Every excitation-sector eigenvalue of the native periodic oriented `Z₂`
Hamiltonian lies above the public exact gap. -/
theorem z2PeriodicHypercubicOriented_native_restricted_eigenvalues_ge_exactGap
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2)
    (j : Fin
      (z2PeriodicHypercubicOrientedNativeScaledHamiltonianGapData
        n hn beta hBeta hBetaLt).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (z2PeriodicHypercubicOrientedNativeScaledHamiltonianGapData
          n hn beta hBeta hBetaLt).toVacuumOrthogonalGapData
        0).eigenvalues
          (z2PeriodicHypercubicOrientedNativeScaledHamiltonianGapData
            n hn beta hBeta hBetaLt).excitedFinrank
          j :=
  finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap
    (z2PeriodicHypercubicOrientedNativeScaledHamiltonianGapData
      n hn beta hBeta hBetaLt)
    0 j

end

end MathlibAnalytic
end MGAP4D
