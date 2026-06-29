import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A proof-relevant Dobrushin influence matrix for one finite
orientation-correct Wilson system.  The entry `influence target source` bounds
how much the exact conditional law at `target` can change when only the
physical `source` link is changed. -/
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

/-- Every row sum of a strict oriented Dobrushin matrix is strictly below one. -/
theorem finite_oriented_dobrushin_rowSum_lt_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    (∑ source : L.Edge, D.influence target source) < 1 :=
  lt_of_le_of_lt (D.rowSum_le_coefficient target)
    D.dobrushinCoefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
