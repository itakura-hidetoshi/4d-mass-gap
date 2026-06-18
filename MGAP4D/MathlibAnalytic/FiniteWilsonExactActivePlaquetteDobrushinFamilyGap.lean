import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonActivePlaquetteDobrushinProfile
import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalDobrushinStrictFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Family-level input expressed through the refined exact off-diagonal
plaquette profile at every Wilson scale. -/
structure FiniteWilsonExactActivePlaquetteDobrushinFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  exactActivePlaquetteProduct_lt_one : ∀ i : W.index,
    ((W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i) : ℝ) *
        (W.system i).canonicalActivePlaquetteInfluenceBound (edgeCard_pos i) < 1

/-- Refined exact active-profile strictness implies strictness of the canonical
Dobrushin coefficient at every finite Wilson scale. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteDobrushinFamilyData.strictFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteDobrushinFamilyData W) :
    FiniteWilsonCanonicalDobrushinStrictFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    coefficient_lt_one := fun i =>
      finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactActivePlaquetteProfile
        (W.system i) (D.edgeCard_pos i)
        (D.exactActivePlaquetteProduct_lt_one i) }

/-- Refined exact active profiles generate the full proof-relevant Dobrushin
matrix family. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteDobrushinFamilyData.matrixFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteDobrushinFamilyData W) :
    FiniteWilsonCanonicalDobrushinMatrixFamilyData W :=
  D.strictFamilyData.matrixFamilyData

/-- Refined exact active profiles generate centered random-scan Rayleigh
certificates at every scale. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteDobrushinFamilyData.rayleighFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteDobrushinFamilyData W) :
    FiniteWilsonDobrushinRandomScanRayleighFamilyData W :=
  D.strictFamilyData.rayleighFamilyData

/-- The refined active-profile inequality implies the normalized Hamiltonian
exact-gap estimate on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_exact_active_plaquette_dobrushin_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonExactActivePlaquetteDobrushinFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.rayleighFamilyData.atScale i) x) x :=
  finite_wilson_canonical_dobrushin_strict_family_hamiltonian_gap
    W D.strictFamilyData i x hx

/-- Canonically generated Hamiltonian gap data from refined active profiles. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteDobrushinFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteDobrushinFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.strictFamilyData.hamiltonianGapData i

/-- Every excitation-sector eigenvalue of the refined-profile normalized
Hamiltonian lies above the public exact gap. -/
theorem finite_wilson_exact_active_plaquette_dobrushin_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonExactActivePlaquetteDobrushinFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_canonical_dobrushin_strict_family_restricted_eigenvalues_ge_exactGap
    W D.strictFamilyData i j

end

end MathlibAnalytic
end MGAP4D
