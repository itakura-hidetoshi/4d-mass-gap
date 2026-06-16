import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A concrete Dobrushin influence matrix for one finite Wilson system.
`influence target source` bounds how much the exact conditional law at
`target` can change when only the `source` link is changed. -/
structure FiniteLatticeWilsonDobrushinMatrixData
    (L : FiniteLatticeWilsonSystem) where
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

/-- The diagonal matrix entry agrees with the exact zero self-influence forced
by off-link fiber invariance. -/
theorem finite_lattice_dobrushin_diagonal_totalVariation_eq
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e =
      D.influence e e := by
  calc
    L.singleLinkConditionalTotalVariation A B e = 0 :=
      finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
        L A B e hAgree
    _ = D.influence e e := (D.influence_diagonal_zero e).symm

/-- Every row sum is strictly below one. -/
theorem finite_lattice_dobrushin_rowSum_lt_one
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    (∑ source : L.Edge, D.influence target source) < 1 :=
  lt_of_le_of_lt (D.rowSum_le_coefficient target)
    D.dobrushinCoefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
