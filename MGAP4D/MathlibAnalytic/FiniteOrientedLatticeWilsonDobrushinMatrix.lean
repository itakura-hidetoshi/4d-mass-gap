import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Proof-relevant Dobrushin matrix data for an orientation-correct finite
Wilson system. -/
structure FiniteOrientedLatticeWilsonDobrushinMatrixData
    (L : FiniteOrientedLatticeWilsonSystem) where
  influence : L.Edge → L.Edge → ℝ
  influence_nonneg :
    ∀ target source : L.Edge, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ e : L.Edge, influence e e = 0
  conditionalTotalVariation_le :
    ∀ (target source : L.Edge) (A B : L.Configuration),
      L.AgreeOffLink A B source →
        L.singleLinkConditionalTotalVariation A B target ≤
          influence target source
  dobrushinCoefficient : ℝ
  dobrushinCoefficient_nonneg : 0 ≤ dobrushinCoefficient
  rowSum_le_coefficient :
    ∀ target : L.Edge,
      ∑ source : L.Edge, influence target source ≤
        dobrushinCoefficient
  dobrushinCoefficient_lt_one : dobrushinCoefficient < 1

/-- The diagonal matrix entry agrees with exact zero self-influence. -/
theorem finite_oriented_dobrushin_diagonal_totalVariation_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e =
      D.influence e e := by
  calc
    L.singleLinkConditionalTotalVariation A B e = 0 :=
      finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
        L A B e hAgree
    _ = D.influence e e := (D.influence_diagonal_zero e).symm

/-- Every row sum in an oriented Dobrushin certificate is below one. -/
theorem finite_oriented_dobrushin_rowSum_lt_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    (∑ source : L.Edge, D.influence target source) < 1 :=
  lt_of_le_of_lt
    (D.rowSum_le_coefficient target)
    D.dobrushinCoefficient_lt_one

/-- A strict exact oriented canonical coefficient generates the complete
proof-relevant Dobrushin matrix certificate. -/
noncomputable def finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1) :
    FiniteOrientedLatticeWilsonDobrushinMatrixData L :=
  { influence := L.canonicalDobrushinInfluence
    influence_nonneg :=
      finite_oriented_canonicalDobrushinInfluence_nonneg L
    influence_diagonal_zero :=
      finite_oriented_canonicalDobrushinInfluence_diagonal L
    conditionalTotalVariation_le := by
      intro target source A B hAgree
      exact
        finite_oriented_singleLinkConditionalTotalVariation_le_canonicalDobrushinInfluence
          L target source A B hAgree
    dobrushinCoefficient := L.canonicalDobrushinCoefficient hEdge
    dobrushinCoefficient_nonneg :=
      finite_oriented_canonicalDobrushinCoefficient_nonneg L hEdge
    rowSum_le_coefficient := by
      intro target
      exact
        finite_oriented_canonicalDobrushinRowSum_le_coefficient
          L hEdge target
    dobrushinCoefficient_lt_one := hStrict }

end

end MathlibAnalytic
end MGAP4D
