import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- A real Hilbert space which is not finite-dimensional contains a countable
orthonormal sequence.

The proof stays entirely inside Mathlib's Hilbert-basis API.  Choose a Hilbert
basis `b : HilbertBasis w ℝ K`.  If its index set `w` were finite, then
`b.toOrthonormalBasis.toBasis` would make `K` finite-dimensional.  Hence `w` is
infinite.  Mathlib's `Infinite.natEmbedding` then selects an injective
`ℕ`-sequence of basis indices, and the corresponding Hilbert-basis vectors are
orthonormal. -/
theorem exists_orthonormal_nat_of_not_finiteDimensional
    {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (hInfiniteDimensional : ¬ FiniteDimensional ℝ K) :
    ∃ e : ℕ → K, Orthonormal ℝ e := by
  classical
  obtain ⟨w, b, _hb⟩ := exists_hilbertBasis ℝ K
  have hwInfinite : w.Infinite := by
    intro hwFinite
    letI : Fintype w := hwFinite.fintype
    apply hInfiniteDimensional
    exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  letI : Infinite w := hwInfinite.to_subtype
  let f : ℕ ↪ w := Infinite.natEmbedding w
  refine ⟨fun n => b (f n), ?_⟩
  constructor
  · intro n
    exact b.orthonormal.norm_eq_one (f n)
  · intro m n hmn
    apply b.orthonormal.inner_eq_zero
    intro hIndex
    apply hmn
    exact f.injective hIndex

/-- Noncomputably select the canonical `ℕ`-indexed orthonormal sequence supplied
by non-finite-dimensionality. -/
noncomputable def orthonormalNatSequenceOfNotFiniteDimensional
    {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (hInfiniteDimensional : ¬ FiniteDimensional ℝ K) : ℕ → K :=
  Classical.choose
    (exists_orthonormal_nat_of_not_finiteDimensional hInfiniteDimensional)

/-- The selected sequence is orthonormal. -/
theorem orthonormalNatSequenceOfNotFiniteDimensional_orthonormal
    {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (hInfiniteDimensional : ¬ FiniteDimensional ℝ K) :
    Orthonormal ℝ
      (orthonormalNatSequenceOfNotFiniteDimensional hInfiniteDimensional) :=
  Classical.choose_spec
    (exists_orthonormal_nat_of_not_finiteDimensional hInfiniteDimensional)

end

end MathlibAnalytic
end MGAP4D
