import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalLocality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A proof-relevant Dobrushin influence matrix for one continuous compact
orientation-correct Wilson system. -/
structure ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData
    (C : ContinuousCompactOrientedGaugeWilsonSystem) where
  influence : C.base.geometry.Edge → C.base.geometry.Edge → ℝ
  influence_nonneg :
    ∀ target source : C.base.geometry.Edge, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ e : C.base.geometry.Edge, influence e e = 0
  conditionalTotalVariation_le :
    ∀ (target source : C.base.geometry.Edge)
      (A B : C.base.Configuration),
      C.base.AgreeOffLink A B source →
        C.singleLinkConditionalTotalVariation A B target ≤
          influence target source
  dobrushinCoefficient : ℝ
  dobrushinCoefficient_nonneg : 0 ≤ dobrushinCoefficient
  rowSum_le_coefficient :
    ∀ target : C.base.geometry.Edge,
      ∑ source : C.base.geometry.Edge, influence target source ≤
        dobrushinCoefficient
  dobrushinCoefficient_lt_one : dobrushinCoefficient < 1

/-- Every row sum of a strict compact oriented Dobrushin matrix is below one. -/
theorem continuous_compact_oriented_dobrushin_rowSum_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target : C.base.geometry.Edge) :
    (∑ source : C.base.geometry.Edge, D.influence target source) < 1 :=
  lt_of_le_of_lt (D.rowSum_le_coefficient target)
    D.dobrushinCoefficient_lt_one

end
end MathlibAnalytic
end MGAP4D
