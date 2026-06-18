import MGAP4D.MathlibAnalytic.FinitePMFLikelihoodRatioTotalVariation
import MGAP4D.MathlibAnalytic.FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Uniform exponential likelihood-ratio control for every realizable active
single-source perturbation of a target Wilson conditional law. -/
def FiniteLatticeWilsonSystem.ActiveConditionalExpRatioBound
    (L : FiniteLatticeWilsonSystem)
    (R : ℝ) : Prop :=
  ∀ (target source : L.Edge) (A : L.Configuration) (g : L.Gauge),
    source ∈ L.activePlaquetteNeighbors target →
      ∀ u : L.Gauge,
        (L.singleLinkConditionalPMF A target u).toReal ≤
            Real.exp R *
              (L.singleLinkConditionalPMF
                (L.replaceLink A source g) target u).toReal ∧
          (L.singleLinkConditionalPMF
              (L.replaceLink A source g) target u).toReal ≤
            Real.exp R *
              (L.singleLinkConditionalPMF A target u).toReal

/-- Pointwise exponential likelihood-ratio control of two Wilson conditionals
implies the sharp finite total-variation estimate. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hAB : ∀ u : L.Gauge,
      (L.singleLinkConditionalPMF A target u).toReal ≤
        Real.exp R * (L.singleLinkConditionalPMF B target u).toReal)
    (hBA : ∀ u : L.Gauge,
      (L.singleLinkConditionalPMF B target u).toReal ≤
        Real.exp R * (L.singleLinkConditionalPMF A target u).toReal) :
    L.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact finite_pmf_totalVariation_le_of_mutual_le_exp_mul
    (L.singleLinkConditionalPMF A target)
    (L.singleLinkConditionalPMF B target)
    R hR hAB hBA

/-- Active conditional exponential-ratio control bounds every exact active
canonical influence by the corresponding sharp TV majorant. -/
theorem finite_lattice_canonicalDobrushinInfluence_le_expRatioBound_of_active
    (L : FiniteLatticeWilsonSystem)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R)
    (target source : L.Edge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  classical
  have hSourceNeTarget : source ≠ target :=
    ((finite_lattice_mem_activePlaquetteNeighbors_iff
      L target source).1 hActive).2
  have hTargetNeSource : target ≠ source := Ne.symm hSourceNeTarget
  rw [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence,
    if_neg hTargetNeSource]
  apply Finset.max'_le
  intro value hValue
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hValue
  rcases Finset.mem_image.mp hValue with ⟨p, _hp, rfl⟩
  apply finite_lattice_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    L p.1 (L.replaceLink p.1 source p.2) target R hR
  · intro u
    exact (hRatio target source p.1 p.2 hActive u).1
  · intro u
    exact (hRatio target source p.1 p.2 hActive u).2

/-- The exact active influence maximum is bounded by the exponential
likelihood-ratio TV majorant. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_le_expRatioBound
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R) :
    L.canonicalActivePlaquetteInfluenceBound hEdge ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceBound
  apply Finset.max'_le
  intro value hValue
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceValues at hValue
  rcases Finset.mem_image.mp hValue with ⟨p, _hp, rfl⟩
  by_cases hActive : p.2 ∈ L.activePlaquetteNeighbors p.1
  · simp only [if_pos hActive]
    exact finite_lattice_canonicalDobrushinInfluence_le_expRatioBound_of_active
      L R hR hRatio p.1 p.2 hActive
  · simp only [if_neg hActive]
    exact expLikelihoodRatioTotalVariationBound_nonneg R hR

/-- An active conditional exponential-ratio bound below the reciprocal active
degree threshold implies strict canonical Dobrushin contraction. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_activeConditionalExpRatio
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hDegreePos : 0 < L.canonicalActivePlaquetteDegree hEdge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) <
        (L.canonicalActivePlaquetteDegree hEdge : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  finite_lattice_canonicalDobrushinCoefficient_lt_one_of_activeInfluence_lt_inv_degree
    L hEdge hDegreePos
      (lt_of_le_of_lt
        (finite_lattice_canonicalActivePlaquetteInfluenceBound_le_expRatioBound
          L hEdge R hR hRatio)
        hThreshold)

/-- Family-level input expressed as a scale-dependent exponential
likelihood-ratio radius for all active Wilson conditional perturbations. -/
structure FiniteWilsonActiveConditionalExpRatioFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  activeDegree_pos : ∀ i : W.index,
    0 < (W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i)
  radius : W.index → ℝ
  radius_nonneg : ∀ i : W.index, 0 ≤ radius i
  activeConditionalExpRatioBound : ∀ i : W.index,
    (W.system i).ActiveConditionalExpRatioBound (radius i)
  expRatioTV_lt_inv_activeDegree : ∀ i : W.index,
    (Real.exp (radius i) - 1) / (Real.exp (radius i) + 1) <
      ((W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i) : ℝ)⁻¹

/-- Convert active conditional exponential-ratio estimates into the reciprocal
active-influence family package consumed by the finite-volume gap spine. -/
noncomputable def
    FiniteWilsonActiveConditionalExpRatioFamilyData.toReciprocalInfluenceFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonActiveConditionalExpRatioFamilyData W) :
    FiniteWilsonExactActivePlaquetteReciprocalInfluenceFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    activeDegree_pos := D.activeDegree_pos
    activeInfluence_lt_inv_degree := fun i =>
      lt_of_le_of_lt
        (finite_lattice_canonicalActivePlaquetteInfluenceBound_le_expRatioBound
          (W.system i) (D.edgeCard_pos i) (D.radius i)
            (D.radius_nonneg i) (D.activeConditionalExpRatioBound i))
        (D.expRatioTV_lt_inv_activeDegree i) }

/-- Active conditional exponential-ratio control generates normalized
Hamiltonian gap data at every finite Wilson scale. -/
noncomputable def
    FiniteWilsonActiveConditionalExpRatioFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonActiveConditionalExpRatioFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.toReciprocalInfluenceFamilyData.hamiltonianGapData i

/-- The active conditional exponential-ratio criterion yields normalized
Hamiltonian exact-gap coercivity on every finite-volume vacuum-orthogonal
sector. -/
theorem finite_wilson_active_conditional_exp_ratio_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonActiveConditionalExpRatioFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.toReciprocalInfluenceFamilyData.toProductFamilyData.rayleighFamilyData.atScale i)
          x) x :=
  finite_wilson_reciprocal_active_influence_family_hamiltonian_gap
    W D.toReciprocalInfluenceFamilyData i x hx

/-- Every excitation-sector eigenvalue generated by the active conditional
exponential-ratio criterion is bounded below by the public exact gap. -/
theorem finite_wilson_active_conditional_exp_ratio_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonActiveConditionalExpRatioFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_reciprocal_active_influence_family_restricted_eigenvalues_ge_exactGap
    W D.toReciprocalInfluenceFamilyData i j

end

end MathlibAnalytic
end MGAP4D
