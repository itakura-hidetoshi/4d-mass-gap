import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u v

/-- A family in a real inner-product space is linearly independent as soon as
every finite subfamily has positive-definite Gram matrix.

Mathlib already characterizes global linear independence by linear independence
of every finite restriction.  On each finite restriction, positive definiteness
of the Gram matrix implies linear independence. -/
theorem linearIndependent_of_finset_gram_posDef
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E)
    (hGram : ∀ s : Finset ι,
      Matrix.PosDef
        (Matrix.gram ℝ (v ∘ (Subtype.val : s → ι)))) :
    LinearIndependent ℝ v := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact Matrix.linearIndependent_of_posDef_gram (hGram s)

/-- Positive definiteness of every finite Gram matrix is exactly global linear
independence.  This finite-local criterion is convenient when the vectors are
OS quotient classes and the matrix entries are reflected Euclidean
correlations. -/
theorem finset_gram_posDef_iff_linearIndependent
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) :
    (∀ s : Finset ι,
      Matrix.PosDef
        (Matrix.gram ℝ (v ∘ (Subtype.val : s → ι)))) ↔
      LinearIndependent ℝ v := by
  constructor
  · exact linearIndependent_of_finset_gram_posDef v
  · intro hv s
    exact Matrix.posDef_gram_of_linearIndependent
      (hv.comp (Subtype.val : s → ι) Subtype.val_injective)

end

end MathlibAnalytic
end MGAP4D
