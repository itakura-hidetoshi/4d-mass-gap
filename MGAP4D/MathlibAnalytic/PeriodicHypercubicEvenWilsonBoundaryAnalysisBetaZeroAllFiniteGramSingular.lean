import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisBetaZeroRankOne
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

/-- At zero coupling, every finite SU(2) primary-plaquette analysis family with
at least two members is linearly dependent.

The proof is purely finite-dimensional.  By the rank-one theorem from the
preceding layer, the range of the whole family lies in the span of one constant
open-half `L²` vector.  Mathlib's `linearIndependent_le_span_aux'` then bounds
the cardinality of any linearly independent family in that span by one. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage_zero_not_linearIndependent_of_one_le
    (H k : ℕ) (hk : 1 ≤ k) :
    ¬ LinearIndependent ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
        H 0 (by norm_num) k) := by
  intro hLI
  let v : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
    periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H 2
  have hspan :
      Set.range
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
            H 0 (by norm_num) k) ⊆
        (Submodule.span ℝ ({v} : Set
          (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))) : Set _) := by
    rintro y ⟨j, rfl⟩
    rw [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage_zero_eq_smul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton v))
  have hcard :=
    linearIndependent_le_span_aux'
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
        H 0 (by norm_num) k)
      hLI
      ({v} : Set (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2)))
      hspan
  have hle : k + 1 ≤ 1 := by
    simpa using hcard
  omega

/-- Hence every actual SU(2) primary-plaquette analysis Gram matrix of size at
least two is singular at zero coupling.  This upgrades the explicit two-mode
calculation from the preceding layer to every finite initial family. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_zero_det_of_one_le
    (H k : ℕ) (hk : 1 ≤ k) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H 0 (by norm_num) k).det = 0 := by
  by_contra hdet
  exact
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage_zero_not_linearIndependent_of_one_le
      H k hk)
      ((periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_iff
        H 0 (by norm_num) k).mp hdet)

/-- Nondegeneracy of any finite initial Gram matrix containing at least two
modes forces strict positivity of the Wilson coupling.

Crucially, `0 < beta` is a *conclusion*, not a new assumption: the existing
`0 ≤ beta` hypothesis and the theorem-proved zero-coupling singularity exclude
the endpoint automatically whenever the determinant route is available. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_implies_beta_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) (hk : 1 ≤ k)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0) :
    0 < beta := by
  have hbeta_ne : beta ≠ 0 := by
    intro hzero
    subst beta
    exact hdet
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_zero_det_of_one_le
        H k hk)
  exact lt_of_le_of_ne hbeta (Ne.symm hbeta_ne)

/-- Scale-sequence form for the physical Wilson interfaces: at any scale where
a `k + 1` mode determinant is nonzero with `k ≥ 1`, the already-nonnegative
scale coupling is automatically strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_implies_scale_beta_pos
    (H : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n k : ℕ) (hk : 1 ≤ k)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        (H n) (beta n) (hbeta n) k).det ≠ 0) :
    0 < beta n :=
  periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_implies_beta_pos
    (H n) (beta n) (hbeta n) k hk hdet

end

end MathlibAnalytic
end MGAP4D
