import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A volume- and lattice-spacing-uniform Dobrushin influence package for a
finite Wilson approximation family. -/
structure FiniteLatticeWilsonApproximationFamily.UniformDobrushinMatrixData
    (F : FiniteLatticeWilsonApproximationFamily) where
  influence :
    (i : F.index) →
      (F.system i).Edge → (F.system i).Edge → ℝ
  influence_nonneg :
    ∀ (i : F.index) (target source : (F.system i).Edge),
      0 ≤ influence i target source
  influence_diagonal_zero :
    ∀ (i : F.index) (e : (F.system i).Edge),
      influence i e e = 0
  conditionalTotalVariation_le :
    ∀ (i : F.index)
      (target source : (F.system i).Edge)
      (A B : (F.system i).Configuration),
      (F.system i).AgreeOffLink A B source →
        (F.system i).singleLinkConditionalTotalVariation A B target ≤
          influence i target source
  dobrushinCoefficient : ℝ
  dobrushinCoefficient_nonneg : 0 ≤ dobrushinCoefficient
  rowSum_le_coefficient :
    ∀ (i : F.index) (target : (F.system i).Edge),
      ∑ source : (F.system i).Edge,
          influence i target source ≤ dobrushinCoefficient
  dobrushinCoefficient_lt_one : dobrushinCoefficient < 1

/-- Restrict uniform Dobrushin data to one finite Wilson system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformDobrushinMatrixData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (D : F.UniformDobrushinMatrixData)
    (i : F.index) :
    FiniteLatticeWilsonDobrushinMatrixData (F.system i) :=
  { influence := D.influence i
    influence_nonneg := D.influence_nonneg i
    influence_diagonal_zero := D.influence_diagonal_zero i
    conditionalTotalVariation_le := D.conditionalTotalVariation_le i
    dobrushinCoefficient := D.dobrushinCoefficient
    dobrushinCoefficient_nonneg := D.dobrushinCoefficient_nonneg
    rowSum_le_coefficient := D.rowSum_le_coefficient i
    dobrushinCoefficient_lt_one := D.dobrushinCoefficient_lt_one }

/-- Every finite scale inherits the same strict row-sum coefficient. -/
theorem finite_lattice_uniform_dobrushin_rowSum_lt_one
    (F : FiniteLatticeWilsonApproximationFamily)
    (D : F.UniformDobrushinMatrixData)
    (i : F.index) (target : (F.system i).Edge) :
    (∑ source : (F.system i).Edge,
        D.influence i target source) < 1 :=
  lt_of_le_of_lt (D.rowSum_le_coefficient i target)
    D.dobrushinCoefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
