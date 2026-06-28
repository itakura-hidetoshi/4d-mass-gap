import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalInfluenceSupport

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Every admissible one-link change is bounded by exact oriented canonical
influence. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_le_canonicalDobrushinInfluence
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalTotalVariation A B target ≤
      L.canonicalDobrushinInfluence target source := by
  classical
  by_cases h : target = source
  · subst target
    rw [finite_oriented_canonicalDobrushinInfluence_diagonal]
    exact le_of_eq
      (finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
        L A B source hAgree)
  · rw [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence,
      if_neg h]
    apply Finset.le_max'
    unfold
      FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues
    apply Finset.mem_image.mpr
    have hReplace : L.replaceLink A source (B source) = B :=
      finite_oriented_replaceLink_right_of_agreeOffLink
        L A B source hAgree
    exact ⟨(A, B source), Finset.mem_univ _, by rw [hReplace]⟩

/-- Exact oriented canonical row sum. -/
def FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) : ℝ :=
  ∑ source : L.Edge, L.canonicalDobrushinInfluence target source

/-- Every exact oriented canonical row sum is nonnegative. -/
theorem finite_oriented_canonicalDobrushinRowSum_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) :
    0 ≤ L.canonicalDobrushinRowSum target := by
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
  exact Finset.sum_nonneg fun source _ =>
    finite_oriented_canonicalDobrushinInfluence_nonneg L target source

/-- The finite set of exact oriented canonical row sums. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums
    (L : FiniteOrientedLatticeWilsonSystem) : Finset ℝ := by
  classical
  exact Finset.univ.image L.canonicalDobrushinRowSum

/-- A nonempty physical-link set yields a nonempty row-sum set. -/
theorem finite_oriented_canonicalDobrushinRowSums_nonempty
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinRowSums.Nonempty := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨L.canonicalDobrushinRowSum e, ?_⟩
  simp [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums]

/-- The exact oriented canonical Dobrushin coefficient is the largest row sum. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℝ :=
  L.canonicalDobrushinRowSums.max'
    (finite_oriented_canonicalDobrushinRowSums_nonempty L hEdge)

/-- Every exact oriented row sum is bounded by the canonical coefficient. -/
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

/-- The exact oriented canonical Dobrushin coefficient is nonnegative. -/
theorem finite_oriented_canonicalDobrushinCoefficient_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ L.canonicalDobrushinCoefficient hEdge := by
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  exact le_trans
    (finite_oriented_canonicalDobrushinRowSum_nonneg L e)
    (finite_oriented_canonicalDobrushinRowSum_le_coefficient L hEdge e)

end

end MathlibAnalytic
end MGAP4D
