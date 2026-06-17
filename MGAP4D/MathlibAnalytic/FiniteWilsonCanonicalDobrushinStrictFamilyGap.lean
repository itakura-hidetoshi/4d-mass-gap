import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalDobrushinMinimality
import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalDobrushinScaledHamiltonianFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The irreducible family-level analytic input after canonical finite
enumeration: nonempty edge sets and strictness of the exact canonical
Dobrushin coefficient at every Wilson scale. -/
structure FiniteWilsonCanonicalDobrushinStrictFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  coefficient_lt_one : ∀ i : W.index,
    (W.system i).canonicalDobrushinCoefficient (edgeCard_pos i) < 1

/-- Strict canonical coefficients generate the full proof-relevant matrix family. -/
noncomputable def
    FiniteWilsonCanonicalDobrushinStrictFamilyData.matrixFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonCanonicalDobrushinStrictFamilyData W) :
    FiniteWilsonCanonicalDobrushinMatrixFamilyData W :=
  { matrixData := fun i =>
      finiteLatticeWilsonCanonicalDobrushinMatrixData
        (W.system i) (D.edgeCard_pos i) (D.coefficient_lt_one i)
    edgeCard_pos := D.edgeCard_pos }

/-- Strict canonical coefficients generate centered random-scan Rayleigh
certificates at every finite Wilson scale. -/
noncomputable def
    FiniteWilsonCanonicalDobrushinStrictFamilyData.rayleighFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonCanonicalDobrushinStrictFamilyData W) :
    FiniteWilsonDobrushinRandomScanRayleighFamilyData W :=
  D.matrixFamilyData.rayleighFamilyData

/-- Strict canonical Dobrushin coefficients imply the normalized Hamiltonian
exact-gap estimate on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_canonical_dobrushin_strict_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonCanonicalDobrushinStrictFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.rayleighFamilyData.atScale i) x) x :=
  finite_wilson_canonical_dobrushin_family_hamiltonian_gap_on_vacuumOrthogonal
    W D.matrixFamilyData i x hx

/-- Canonically generated finite-volume gap data from strict scalar
coefficients alone. -/
noncomputable def
    FiniteWilsonCanonicalDobrushinStrictFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonCanonicalDobrushinStrictFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.matrixFamilyData.hamiltonianGapData i

/-- At every finite Wilson scale, all excitation-sector eigenvalues of the
canonically generated normalized Hamiltonian lie above the public exact gap. -/
theorem finite_wilson_canonical_dobrushin_strict_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonCanonicalDobrushinStrictFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_canonical_dobrushin_family_restricted_eigenvalues_ge_exactGap
    W D.matrixFamilyData i j

end

end MathlibAnalytic
end MGAP4D
