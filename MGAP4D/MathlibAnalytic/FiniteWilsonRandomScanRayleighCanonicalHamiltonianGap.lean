import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Package centered random-scan Rayleigh contraction as the canonical finite
Wilson Gibbs-Hilbert Hamiltonian bridge at one lattice scale. -/
noncomputable def finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData (W.system i)) :
    FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData W i :=
  finiteWilsonCanonicalHeatBathHamiltonianBridgeData W i
    (finite_lattice_exactGap_heatBathPoincare_of_randomScanRayleighContraction
      (W.system i) R)

/-- Centered random-scan Rayleigh contraction implies the canonical
vacuum-centered Hamiltonian lower bound. -/
theorem finite_wilson_randomScanRayleigh_implies_canonical_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData (W.system i))
    (x : (W.system i).GibbsHilbertSpace) :
    exactGapValueReal *
        ‖finiteVacuumCentered (W.system i).gibbsHilbertVacuum x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsHeatBathHamiltonianLinearMap x) x :=
  finite_wilson_exact_heat_bath_poincare_implies_canonical_hamiltonian_gap
    W i
      (finite_lattice_exactGap_heatBathPoincare_of_randomScanRayleighContraction
        (W.system i) R)
      x

/-- On the physical excitation sector, centered random-scan Rayleigh
contraction gives the exact canonical Hamiltonian coercive estimate. -/
theorem finite_wilson_randomScanRayleigh_implies_canonical_hamiltonian_gap_on_vacuumOrthogonal
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData (W.system i))
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsHeatBathHamiltonianLinearMap x) x := by
  have hOrth :
      inner ℝ (W.system i).gibbsHilbertVacuum x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      (W.system i).gibbsHilbertVacuum x).mp hx
  simpa [finiteVacuumCentered, hOrth] using
    (finite_wilson_randomScanRayleigh_implies_canonical_hamiltonian_gap
      W i R x)

/-- Every excitation-sector eigenvalue of the canonical finite Wilson
heat-bath Hamiltonian inherits the exact lower bound from centered random-scan
Rayleigh contraction. -/
theorem finite_wilson_randomScanRayleigh_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData (W.system i))
    (j : Fin
      (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
        W i R).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
          W i R).toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData
        0).eigenvalues
          (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData
            W i R).excitedFinrank
          j :=
  finite_wilson_concrete_gibbs_hilbert_restricted_eigenvalues_ge_exactGap
    (finiteWilsonRandomScanRayleighCanonicalHamiltonianBridgeData W i R)
    0 j

end

end MathlibAnalytic
end MGAP4D
