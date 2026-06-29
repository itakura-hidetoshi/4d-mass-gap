import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalFiberInvariance
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every admissible one-link perturbation is dominated by the exact oriented canonical influence. -/
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
  · rw [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence, if_neg h]
    apply Finset.le_max'
    unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues
    apply Finset.mem_image.mpr
    have hReplace : L.replaceLink A source (B source) = B :=
      finite_oriented_replaceLink_right_of_agreeOffLink L A B source hAgree
    exact ⟨(A, B source), Finset.mem_univ _, by rw [hReplace]⟩

/-- A strict exact oriented canonical coefficient generates the complete proof-relevant matrix certificate. -/
noncomputable def finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1) :
    FiniteOrientedLatticeWilsonDobrushinMatrixData L :=
  { influence := L.canonicalDobrushinInfluence
    influence_nonneg := finite_oriented_canonicalDobrushinInfluence_nonneg L
    influence_diagonal_zero := finite_oriented_canonicalDobrushinInfluence_diagonal L
    conditionalTotalVariation_le := by
      intro target source A B hAgree
      exact finite_oriented_singleLinkConditionalTotalVariation_le_canonicalDobrushinInfluence
        L target source A B hAgree
    dobrushinCoefficient := L.canonicalDobrushinCoefficient hEdge
    dobrushinCoefficient_nonneg :=
      finite_oriented_canonicalDobrushinCoefficient_nonneg L hEdge
    rowSum_le_coefficient := by
      intro target
      exact finite_oriented_canonicalDobrushinRowSum_le_coefficient L hEdge target
    dobrushinCoefficient_lt_one := hStrict }

end

end MathlibAnalytic
end MGAP4D
