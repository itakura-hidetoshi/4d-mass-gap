import MGAP4D.MathlibAnalytic.FiniteWilsonDobrushinScaledHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A centered Dobrushin random-scan Rayleigh certificate at every finite
Wilson approximation scale. -/
structure FiniteWilsonDobrushinRandomScanRayleighFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  atScale : ∀ i : W.index,
    FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate (W.system i)

/-- At every finite Wilson scale, the Dobrushin heat-bath gap controls the
finite Gibbs variance by the exact heat-bath Dirichlet form. -/
theorem finite_wilson_dobrushin_family_heatBathGap_mul_variance_le_dirichlet
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (C : FiniteWilsonDobrushinRandomScanRayleighFamilyData W)
    (i : W.index)
    (f : (W.system i).Configuration → ℝ) :
    finiteLatticeWilsonDobrushinHeatBathGap (C.atScale i).matrixData *
        (W.system i).gibbsVarianceReal f ≤
      (W.system i).singleLinkHeatBathDirichletForm f :=
  finite_lattice_dobrushinHeatBathGap_mul_variance_le_dirichlet
    (W.system i) (C.atScale i) f

/-- At every finite Wilson scale, the explicitly normalized Dobrushin
Hamiltonian quadratic form carries the public exact-gap coefficient. -/
theorem finite_wilson_dobrushin_family_exactGap_mul_variance_le_scaled_dirichlet
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (C : FiniteWilsonDobrushinRandomScanRayleighFamilyData W)
    (i : W.index)
    (f : (W.system i).Configuration → ℝ) :
    exactGapValueReal * (W.system i).gibbsVarianceReal f ≤
      finiteLatticeWilsonDobrushinNormalizedScale
          (C.atScale i).matrixData *
        (W.system i).singleLinkHeatBathDirichletForm f :=
  finite_lattice_exactGap_mul_variance_le_dobrushinScale_mul_dirichlet
    (W.system i) (C.atScale i) f

/-- The normalized Dobrushin Hamiltonian has the same public lower bound on
every finite-volume vacuum-orthogonal excitation sector. -/
theorem finite_wilson_dobrushin_family_hamiltonian_gap_on_vacuumOrthogonal
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (C : FiniteWilsonDobrushinRandomScanRayleighFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (C.atScale i) x) x :=
  finite_lattice_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
    (W.system i) (C.atScale i) x hx

/-- Package the normalized Dobrushin Hamiltonian gap data at every finite
approximation scale. -/
noncomputable def
    FiniteWilsonDobrushinRandomScanRayleighFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (C : FiniteWilsonDobrushinRandomScanRayleighFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  finiteWilsonDobrushinScaledHamiltonianGapData W i (C.atScale i)

/-- Every excitation-sector eigenvalue at every finite Wilson scale lies above
the same public exact gap after the explicit Dobrushin normalization. -/
theorem finite_wilson_dobrushin_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (C : FiniteWilsonDobrushinRandomScanRayleighFamilyData W)
    (i : W.index)
    (j : Fin (C.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (C.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (C.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap
    (C.hamiltonianGapData i) 0 j

end

end MathlibAnalytic
end MGAP4D
