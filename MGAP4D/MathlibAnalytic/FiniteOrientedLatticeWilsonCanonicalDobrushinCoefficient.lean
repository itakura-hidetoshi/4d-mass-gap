import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalInfluenceBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Replacing one physical source link changes no other physical link. -/
theorem finite_oriented_agreeOffLink_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (source : L.Edge)
    (g : L.Gauge) :
    L.AgreeOffLink A (L.replaceLink A source g) source := by
  intro e he
  symm
  exact finite_oriented_replaceLink_of_ne L A source e g he

/-- A source outside the target plaquette neighborhood does not change the
real-valued exact target conditional law. -/
theorem finite_oriented_singleLinkConditionalPMF_toReal_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source)
    (u : L.Gauge) :
    (L.singleLinkConditionalPMF A target u).toReal =
      (L.singleLinkConditionalPMF B target u).toReal := by
  have hLogWeight :
      L.targetLocalSingleLinkLogWeight A target =
        L.targetLocalSingleLinkLogWeight B target := by
    funext g
    unfold FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight
    rw [finite_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
      L A B target source g hNotNeighbor hAgree]
  calc
    (L.singleLinkConditionalPMF A target u).toReal =
        finiteNormalizedExp (L.targetLocalSingleLinkLogWeight A target) u :=
      finite_oriented_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp
        L A target u
    _ = finiteNormalizedExp (L.targetLocalSingleLinkLogWeight B target) u := by
      rw [hLogWeight]
    _ = (L.singleLinkConditionalPMF B target u).toReal :=
      (finite_oriented_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp
        L B target u).symm

/-- Conditional total variation is exactly zero for a source outside the target
plaquette neighborhood. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalTotalVariation A B target = 0 := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
  simp [finite_oriented_singleLinkConditionalPMF_toReal_eq_of_not_neighbor
    L A B target source hNotNeighbor hAgree]

/-- The exact oriented canonical influence vanishes outside the active
plaquette-neighbor support. -/
theorem finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_active
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge)
    (hInactive : source ∉ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source = 0 := by
  classical
  by_cases hTargetSource : target = source
  · subst source
    exact finite_oriented_canonicalDobrushinInfluence_diagonal L target
  · have hSourceTarget : source ≠ target := Ne.symm hTargetSource
    have hNotNeighbor : source ∉ L.plaquetteNeighbors target := by
      intro hNeighbor
      apply hInactive
      exact (finite_oriented_mem_activePlaquetteNeighbors_iff
        L target source).2
          ⟨(finite_oriented_mem_plaquetteNeighbors_iff
              L target source).1 hNeighbor,
            hSourceTarget⟩
    rw [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence,
      if_neg hTargetSource]
    apply le_antisymm
    · apply Finset.max'_le
      intro value hValue
      unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hValue
      rcases Finset.mem_image.mp hValue with ⟨p, _hp, rfl⟩
      exact le_of_eq
        (finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_not_neighbor
          L p.1 (L.replaceLink p.1 source p.2) target source hNotNeighbor
          (finite_oriented_agreeOffLink_replaceLink L p.1 source p.2))
    · exact finite_oriented_canonicalDobrushinInfluence_nonneg L target source

/-- Canonical row sum of exact orientation-correct single-link influences. -/
def FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) : ℝ :=
  ∑ source : L.Edge, L.canonicalDobrushinInfluence target source

/-- Every orientation-correct canonical row sum is nonnegative. -/
theorem finite_oriented_canonicalDobrushinRowSum_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) :
    0 ≤ L.canonicalDobrushinRowSum target := by
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
  exact Finset.sum_nonneg fun source _ =>
    finite_oriented_canonicalDobrushinInfluence_nonneg L target source

/-- The canonical row sum is supported exactly on active plaquette neighbors. -/
theorem finite_oriented_canonicalDobrushinRowSum_eq_sum_active
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target =
      ∑ source in L.activePlaquetteNeighbors target,
        L.canonicalDobrushinInfluence target source := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro source _hUniv hInactive
  exact finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_active
    L target source hInactive

/-- A uniform active-influence majorant bounds the exact row sum by active
degree times that majorant. -/
theorem finite_oriented_canonicalDobrushinRowSum_le_card_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (eta : ℝ)
    (hInfluence : ∀ source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta) :
    L.canonicalDobrushinRowSum target ≤
      ((L.activePlaquetteNeighbors target).card : ℝ) * eta := by
  classical
  rw [finite_oriented_canonicalDobrushinRowSum_eq_sum_active]
  calc
    (∑ source in L.activePlaquetteNeighbors target,
        L.canonicalDobrushinInfluence target source) ≤
        ∑ _source in L.activePlaquetteNeighbors target, eta := by
      exact Finset.sum_le_sum fun source hSource => hInfluence source hSource
    _ = ((L.activePlaquetteNeighbors target).card : ℝ) * eta := by
      simp

/-- The finite set of all orientation-correct canonical row sums. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums
    (L : FiniteOrientedLatticeWilsonSystem) : Finset ℝ := by
  classical
  exact Finset.univ.image L.canonicalDobrushinRowSum

/-- A nonempty physical-link set gives a nonempty finite set of oriented row
sums. -/
theorem finite_oriented_canonicalDobrushinRowSums_nonempty
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinRowSums.Nonempty := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨L.canonicalDobrushinRowSum e, ?_⟩
  simp [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums]

/-- The orientation-correct canonical Dobrushin coefficient is the largest
exact influence row sum. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℝ :=
  L.canonicalDobrushinRowSums.max'
    (finite_oriented_canonicalDobrushinRowSums_nonempty L hEdge)

/-- Every exact oriented row sum is bounded by the oriented canonical
coefficient. -/
theorem finite_oriented_canonicalDobrushinRowSum_le_coefficient
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤
      L.canonicalDobrushinCoefficient hEdge := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.le_max'
  simp [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums]

/-- The orientation-correct canonical Dobrushin coefficient is nonnegative. -/
theorem finite_oriented_canonicalDobrushinCoefficient_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ L.canonicalDobrushinCoefficient hEdge := by
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  exact le_trans
    (finite_oriented_canonicalDobrushinRowSum_nonneg L e)
    (finite_oriented_canonicalDobrushinRowSum_le_coefficient L hEdge e)

/-- A uniform active-degree bound and active-influence majorant bound the exact
orientation-correct canonical coefficient. -/
theorem finite_oriented_canonicalDobrushinCoefficient_le_degree_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (degree : ℕ)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hDegree : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degree)
    (hInfluence : ∀ (target source : L.Edge),
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta) :
    L.canonicalDobrushinCoefficient hEdge ≤ (degree : ℝ) * eta := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.max'_le
  intro value hValue
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums at hValue
  rcases Finset.mem_image.mp hValue with ⟨target, _hTarget, rfl⟩
  exact le_trans
    (finite_oriented_canonicalDobrushinRowSum_le_card_mul
      L target eta (hInfluence target))
    (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (hDegree target)) hEta)

/-- The scalar degree-majorant inequality below one is a complete strictness
certificate for the exact orientation-correct canonical coefficient. -/
theorem finite_oriented_canonicalDobrushinCoefficient_lt_one_of_degree_mul_lt_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (degree : ℕ)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hDegree : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degree)
    (hInfluence : ∀ (target source : L.Edge),
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta)
    (hStrict : (degree : ℝ) * eta < 1) :
    L.canonicalDobrushinCoefficient hEdge < 1 := by
  exact lt_of_le_of_lt
    (finite_oriented_canonicalDobrushinCoefficient_le_degree_mul
      L hEdge degree eta hEta hDegree hInfluence)
    hStrict

end

end MathlibAnalytic
end MGAP4D
