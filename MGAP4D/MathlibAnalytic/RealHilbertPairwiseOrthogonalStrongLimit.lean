import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Pairwise-orthogonal strong-limit obstruction

A sequence which moves through mutually orthogonal Hilbert directions cannot
converge strongly to a nonzero vector.  This elementary fact is useful when a
"common carrier" is built as an independent product and distinct cutoff scales
are placed in distinct coordinate directions.

The theorem is intentionally model-free.  Wilson-specific coordinate
orthogonality is proved separately, so no probabilistic or physical
identification is hidden in this Hilbert-space lemma.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open scoped InnerProductSpace

/-- A strongly convergent sequence of pairwise orthogonal vectors in a real
Hilbert space has zero limit.

No normalization or completeness assumption is needed. -/
theorem realHilbert_tendsto_zero_of_pairwise_inner_eq_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : ℕ → E)
    (x : E)
    (horth : ∀ {m n : ℕ}, m ≠ n → inner ℝ (v m) (v n) = 0)
    (hlim : Tendsto v atTop (𝓝 x)) :
    x = 0 := by
  have hmx : ∀ m : ℕ, inner ℝ (v m) x = 0 := by
    intro m
    have hinner :
        Tendsto
          (fun n : ℕ => inner ℝ (v m) (v n))
          atTop
          (𝓝 (inner ℝ (v m) x)) :=
      tendsto_const_nhds.inner hlim
    have heventually :
        (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => inner ℝ (v m) (v n)) := by
      filter_upwards [eventually_ge_atTop (m + 1)] with n hn
      have hne : m ≠ n := by
        omega
      exact (horth hne).symm
    have hzero :
        Tendsto
          (fun n : ℕ => inner ℝ (v m) (v n))
          atTop
          (𝓝 0) :=
      tendsto_const_nhds.congr' heventually
    exact tendsto_nhds_unique hinner hzero
  have hselfLimit :
      Tendsto
        (fun m : ℕ => inner ℝ (v m) x)
        atTop
        (𝓝 (inner ℝ x x)) :=
    hlim.inner tendsto_const_nhds
  have hzeroLimit :
      Tendsto
        (fun m : ℕ => inner ℝ (v m) x)
        atTop
        (𝓝 0) := by
    have hfun :
        (fun m : ℕ => inner ℝ (v m) x) =
          (fun _ : ℕ => (0 : ℝ)) := by
      funext m
      exact hmx m
    rw [hfun]
    exact tendsto_const_nhds
  have hself : inner ℝ x x = 0 :=
    tendsto_nhds_unique hselfLimit hzeroLimit
  have hnormSq : ‖x‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hself
  have hnorm : ‖x‖ = 0 := by
    nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hnorm

end MathlibAnalytic
end MGAP4D
