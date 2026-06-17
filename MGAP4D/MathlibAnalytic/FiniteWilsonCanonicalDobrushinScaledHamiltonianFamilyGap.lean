import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalRandomScanRayleighSpectralLift
import MGAP4D.MathlibAnalytic.FiniteWilsonDobrushinScaledHamiltonianFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The remaining finite-scale input for the canonical Dobrushin Hamiltonian
lane: a strict Dobrushin matrix and a nonempty edge set at every Wilson scale. -/
structure FiniteWilsonCanonicalDobrushinMatrixFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  matrixData : ∀ i : W.index,
    FiniteLatticeWilsonDobrushinMatrixData (W.system i)
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge

/-- Canonical variation and the finite-dimensional spectral theorem generate
the centered random-scan Rayleigh certificate at every finite Wilson scale. -/
noncomputable def
    FiniteWilsonCanonicalDobrushinMatrixFamilyData.rayleighFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonCanonicalDobrushinMatrixFamilyData W) :
    FiniteWilsonDobrushinRandomScanRayleighFamilyData W :=
  { atScale := fun i =>
      finiteLatticeWilsonCanonicalDobrushinRandomScanRayleighCertificate
        (W.system i) (D.matrixData i) (D.edgeCard_pos i) }

/-- At every finite Wilson scale, the canonical Dobrushin data now imply the
unnormalized heat-bath Poincare inequality directly. -/
theorem finite_wilson_canonical_dobrushin_family_heatBathGap_mul_variance_le_dirichlet
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonCanonicalDobrushinMatrixFamilyData W)
    (i : W.index)
    (f : (W.system i).Configuration → ℝ) :
    finiteLatticeWilsonDobrushinHeatBathGap (D.matrixData i) *
        (W.system i).gibbsVarianceReal f ≤
      (W.system i).singleLinkHeatBathDirichletForm f :=
  finite_wilson_dobrushin_family_heatBathGap_mul_variance_le_dirichlet
    W D.rayleighFamilyData i f

/-- After the explicit positive normalization, the canonical Dobrushin family
carries the repository's public exact-gap coefficient at every finite scale. -/
theorem finite_wilson_canonical_dobrushin_family_exactGap_mul_variance_le_scaled_dirichlet
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonCanonicalDobrushinMatrixFamilyData W)
    (i : W.index)
    (f : (W.system i).Configuration → ℝ) :
    exactGapValueReal * (W.system i).gibbsVarianceReal f ≤
      finiteLatticeWilsonDobrushinNormalizedScale (D.matrixData i) *
        (W.system i).singleLinkHeatBathDirichletForm f :=
  finite_wilson_dobrushin_family_exactGap_mul_variance_le_scaled_dirichlet
    W D.rayleighFamilyData i f

/-- The canonically generated normalized Dobrushin Hamiltonian has the public
exact lower bound on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_canonical_dobrushin_family_hamiltonian_gap_on_vacuumOrthogonal
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonCanonicalDobrushinMatrixFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.rayleighFamilyData.atScale i) x) x :=
  finite_wilson_dobrushin_family_hamiltonian_gap_on_vacuumOrthogonal
    W D.rayleighFamilyData i x hx

/-- Canonically generated finite-volume Hamiltonian gap data at scale `i`. -/
noncomputable def
    FiniteWilsonCanonicalDobrushinMatrixFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonCanonicalDobrushinMatrixFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.rayleighFamilyData.hamiltonianGapData i

/-- Every excitation-sector eigenvalue of the canonically generated normalized
Dobrushin Hamiltonian lies above the same public exact gap at every finite
Wilson scale. -/
theorem finite_wilson_canonical_dobrushin_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonCanonicalDobrushinMatrixFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_dobrushin_family_restricted_eigenvalues_ge_exactGap
    W D.rayleighFamilyData i j

end

end MathlibAnalytic
end MGAP4D
