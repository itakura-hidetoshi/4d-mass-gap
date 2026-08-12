import Mathlib.LinearAlgebra.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

/-- A finite family in a real inner-product space is linearly independent once
every nontrivial scalar combination is detected by some inner-product probe.

This is a purely finite-dimensional-index separation lemma; the ambient inner-
product space itself need not be finite-dimensional or complete. -/
theorem finite_real_inner_probe_separation_linearIndependent
    {ι E : Type*}
    [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [InnerProductSpace ℝ E]
    (v : ι → E)
    (hsep :
      ∀ c : ι → ℝ, c ≠ 0 →
        ∃ q : E, inner ℝ q (∑ i, c i • v i) ≠ 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  have hc0 : c = 0 := by
    by_contra hc
    rcases hsep c hc with ⟨q, hq⟩
    apply hq
    rw [hsum, inner_zero]
  intro i
  simpa using congrFun hc0 i

/-- Contrapositive-friendly form: if a finite family is not linearly
independent, then some nonzero coefficient family gives a combination invisible
to every inner-product probe. -/
theorem finite_real_inner_probe_not_separated_of_not_linearIndependent
    {ι E : Type*}
    [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [InnerProductSpace ℝ E]
    (v : ι → E)
    (hdep : ¬ LinearIndependent ℝ v) :
    ∃ c : ι → ℝ, c ≠ 0 ∧
      ∀ q : E, inner ℝ q (∑ i, c i • v i) = 0 := by
  contrapose! hdep
  exact finite_real_inner_probe_separation_linearIndependent v hdep

end

end MathlibAnalytic
end MGAP4D
