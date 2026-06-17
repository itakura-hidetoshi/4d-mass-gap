import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanRayleighCanonicalHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Centered random-scan Rayleigh certificates at every finite Wilson scale. -/
structure FiniteWilsonRandomScanRayleighContractionFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  atScale : ∀ i : W.index,
    FiniteLatticeWilsonRandomScanRayleighContractionData (W.system i)

/-- The family certificate yields the exact heat-bath Poincare inequality at
all finite approximation scales. -/
theorem finite_wilson_randomScanRayleigh_family_exactGap_heatBathPoincare
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (R : FiniteWilsonRandomScanRayleighContractionFamilyData W)
    (i : W.index) :
    (W.system i).ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_randomScanRayleighContraction
    (W.system i) (R.atScale i)

/-- The family certificate yields canonical Hamiltonian coercivity on every
vacuum-orthogonal finite-volume excitation sector. -/
theorem finite_wilson_randomScanRayleigh_family_hamiltonian_gap_on_vacuumOrthogonal
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (R : FiniteWilsonRandomScanRayleighContractionFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ ((W.system i).gibbsHeatBathHamiltonianLinearMap x) x :=
  finite_wilson_randomScanRayleigh_implies_canonical_hamiltonian_gap_on_vacuumOrthogonal
    W i (R.atScale i) x hx

/-- Every excitation-sector eigenvalue at every finite Wilson scale obeys the
same exact lower bound. -/
theorem finite_wilson_randomScanRayleigh_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (R : FiniteWilsonRandomScanRayleighContractionFamilyData W)
    (i : W.index)
    (j : Fin
      (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
        W i (R.atScale i)).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
          W i (R.atScale i)).toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData
        0).eigenvalues
          (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
            W i (R.atScale i)).excitedFinrank
          j :=
  finite_wilson_randomScanRayleigh_restricted_eigenvalues_ge_exactGap
    W i (R.atScale i) j

end

end MathlibAnalytic
end MGAP4D
