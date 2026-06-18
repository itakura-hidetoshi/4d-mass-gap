import MGAP4D.MathlibAnalytic.FiniteWilsonExactActivePlaquetteDobrushinFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The refined active off-diagonal influence maximum is still a probability
variation quantity, hence is at most one. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_le_one
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteInfluenceBound hEdge ≤ 1 :=
  le_trans
    (finite_lattice_canonicalActivePlaquetteInfluenceBound_le_canonicalPlaquetteLocalInfluenceBound
      L hEdge)
    (finite_lattice_canonicalPlaquetteLocalInfluenceBound_le_one L hEdge)

/-- The exact active local influence maximum belongs to the unit interval. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_mem_unitInterval
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteInfluenceBound hEdge ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finite_lattice_canonicalActivePlaquetteInfluenceBound_nonneg L hEdge,
    finite_lattice_canonicalActivePlaquetteInfluenceBound_le_one L hEdge⟩

/-- The analytically natural reciprocal criterion
`η_active < 1 / d_active` implies the exact product criterion
`d_active * η_active < 1`. -/
theorem finite_lattice_exactActivePlaquetteProduct_lt_one_of_influence_lt_inv_degree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hDegreePos : 0 < L.canonicalActivePlaquetteDegree hEdge)
    (hInfluence :
      L.canonicalActivePlaquetteInfluenceBound hEdge <
        (L.canonicalActivePlaquetteDegree hEdge : ℝ)⁻¹) :
    (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
        L.canonicalActivePlaquetteInfluenceBound hEdge < 1 := by
  have hDegreeReal :
      0 < (L.canonicalActivePlaquetteDegree hEdge : ℝ) := by
    exact_mod_cast hDegreePos
  calc
    (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
          L.canonicalActivePlaquetteInfluenceBound hEdge <
        (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
          (L.canonicalActivePlaquetteDegree hEdge : ℝ)⁻¹ :=
      mul_lt_mul_of_pos_left hInfluence hDegreeReal
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hDegreeReal)

/-- The reciprocal active-influence criterion directly implies strict canonical
Dobrushin contraction. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_activeInfluence_lt_inv_degree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hDegreePos : 0 < L.canonicalActivePlaquetteDegree hEdge)
    (hInfluence :
      L.canonicalActivePlaquetteInfluenceBound hEdge <
        (L.canonicalActivePlaquetteDegree hEdge : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactActivePlaquetteProfile
    L hEdge
      (finite_lattice_exactActivePlaquetteProduct_lt_one_of_influence_lt_inv_degree
        L hEdge hDegreePos hInfluence)

/-- Family-level analytic input in its reciprocal form.  This is the precise
interface expected from a quantitative plaquette-energy estimate. -/
structure FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  activeDegree_pos : ∀ i : W.index,
    0 < (W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i)
  activeInfluence_lt_inv_degree : ∀ i : W.index,
    (W.system i).canonicalActivePlaquetteInfluenceBound (edgeCard_pos i) <
      ((W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i) : ℝ)⁻¹

/-- Convert the reciprocal analytic criterion into the exact active-product
family package already consumed by the gap spine. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData.toProductFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData W) :
    FiniteWilsonExactActivePlaquetteDobrushinFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    exactActivePlaquetteProduct_lt_one := fun i =>
      finite_lattice_exactActivePlaquetteProduct_lt_one_of_influence_lt_inv_degree
        (W.system i) (D.edgeCard_pos i) (D.activeDegree_pos i)
          (D.activeInfluence_lt_inv_degree i) }

/-- Reciprocal active-influence estimates generate the proof-relevant strict
Dobrushin family. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData.strictFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData W) :
    FiniteWilsonCanonicalDobrushinStrictFamilyData W :=
  D.toProductFamilyData.strictFamilyData

/-- Reciprocal active-influence estimates generate normalized Hamiltonian gap
data at every finite Wilson scale. -/
noncomputable def
    FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.toProductFamilyData.hamiltonianGapData i

/-- The reciprocal criterion yields the normalized Hamiltonian exact-gap
coercivity estimate on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_reciprocal_active_influence_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.toProductFamilyData.rayleighFamilyData.atScale i) x) x :=
  finite_wilson_exact_active_plaquette_dobrushin_family_hamiltonian_gap
    W D.toProductFamilyData i x hx

/-- Every excitation-sector eigenvalue generated by the reciprocal criterion is
bounded below by the public exact gap. -/
theorem finite_wilson_reciprocal_active_influence_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_exact_active_plaquette_dobrushin_family_restricted_eigenvalues_ge_exactGap
    W D.toProductFamilyData i j

end

end MathlibAnalytic
end MGAP4D
