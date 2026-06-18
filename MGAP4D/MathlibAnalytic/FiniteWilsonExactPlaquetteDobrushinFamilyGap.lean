import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonExactPlaquetteDobrushinProfile
import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalDobrushinStrictFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Family-level Wilson input expressed entirely through the exact finite
plaquette profile at each scale. -/
structure FiniteWilsonExactPlaquetteDobrushinFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  exactPlaquetteProduct_lt_one : ∀ i : W.index,
    ((W.system i).canonicalPlaquetteDegree (edgeCard_pos i) : ℝ) *
        (W.system i).canonicalPlaquetteLocalInfluenceBound (edgeCard_pos i) < 1

/-- Exact plaquette-profile strictness implies strictness of the canonical
Dobrushin coefficient at every Wilson scale. -/
noncomputable def FiniteWilsonExactPlaquetteDobrushinFamilyData.strictFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactPlaquetteDobrushinFamilyData W) :
    FiniteWilsonCanonicalDobrushinStrictFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    coefficient_lt_one := fun i =>
      finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactPlaquetteProfile
        (W.system i) (D.edgeCard_pos i)
        (D.exactPlaquetteProduct_lt_one i) }

/-- Exact plaquette profiles generate the full canonical Dobrushin matrix
family. -/
noncomputable def FiniteWilsonExactPlaquetteDobrushinFamilyData.matrixFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactPlaquetteDobrushinFamilyData W) :
    FiniteWilsonCanonicalDobrushinMatrixFamilyData W :=
  D.strictFamilyData.matrixFamilyData

/-- Exact plaquette profiles generate centered random-scan Rayleigh
certificates at every finite Wilson scale. -/
noncomputable def FiniteWilsonExactPlaquetteDobrushinFamilyData.rayleighFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactPlaquetteDobrushinFamilyData W) :
    FiniteWilsonDobrushinRandomScanRayleighFamilyData W :=
  D.strictFamilyData.rayleighFamilyData

/-- The exact plaquette-profile inequality implies the normalized Hamiltonian
exact-gap estimate on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_exact_plaquette_dobrushin_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonExactPlaquetteDobrushinFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.rayleighFamilyData.atScale i) x) x :=
  finite_wilson_canonical_dobrushin_strict_family_hamiltonian_gap
    W D.strictFamilyData i x hx

/-- Canonically generated finite-volume Hamiltonian gap data from exact
plaquette profiles. -/
noncomputable def
    FiniteWilsonExactPlaquetteDobrushinFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactPlaquetteDobrushinFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.strictFamilyData.hamiltonianGapData i

/-- Every excitation-sector eigenvalue of the exact-profile normalized
Hamiltonian lies above the public exact gap at every finite Wilson scale. -/
theorem finite_wilson_exact_plaquette_dobrushin_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonExactPlaquetteDobrushinFamilyData W)
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
