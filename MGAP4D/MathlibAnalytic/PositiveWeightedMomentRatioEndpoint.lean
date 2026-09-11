import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter
open scoped Topology BigOperators

noncomputable section

universe u

/-- Abstract endpoint principle for positive weighted moment ratios.

Let `m n` be a strictly positive moment sequence whose successive ratios are
nondecreasing and bounded above.  Suppose every visible coordinate `x i`
(weight `a i > 0`) contributes the lower bound

`a i * (x i)^n ≤ m n`

at every order, and let `S` be no larger than every common upper bound of the
visible coordinates.  If every successive ratio is at most `S`, then the
ratio sequence converges exactly to `S`.

The key point is that the supremum `L` of the ratio sequence must dominate
every visible coordinate.  Otherwise `L < x i`; positivity gives `L > 0`,
while the ratio bound yields `m n ≤ m 0 * L^n`.  The visible-coordinate lower
bound then makes `(x i / L)^n` uniformly bounded, contradicting
`tendsto_pow_atTop_atTop_of_one_lt` because `x i / L > 1`.

This theorem deliberately separates the asymptotic real-analysis core from
any particular `tsum` representation.  The spectral-resolvent specialization
only has to supply the pointwise moment lower bounds, ratio monotonicity, and
the visible-coordinate least-upper-bound property. -/
theorem positiveWeightedMomentRatio_tendsto_of_supremum
    {ι : Type u}
    (m : ℕ → ℝ)
    (a x : ι → ℝ)
    (S : ℝ)
    (hpos : ∀ n : ℕ, 0 < m n)
    (hcoord : ∀ i : ι, 0 < a i → ∀ n : ℕ, a i * x i ^ n ≤ m n)
    (hmono : Monotone (fun n : ℕ => m (n + 1) / m n))
    (hupper : ∀ n : ℕ, m (n + 1) / m n ≤ S)
    (hLeastVisibleUpper :
      ∀ b : ℝ, (∀ i : ι, 0 < a i → x i ≤ b) → S ≤ b) :
    Tendsto (fun n : ℕ => m (n + 1) / m n) atTop (𝓝 S) := by
  let r : ℕ → ℝ := fun n => m (n + 1) / m n
  let L : ℝ := sSup (Set.range r)
  have hrpos : ∀ n : ℕ, 0 < r n := by
    intro n
    exact div_pos (hpos (n + 1)) (hpos n)
  have hmono' : Monotone r := by
    simpa [r] using hmono
  have hbdd : BddAbove (Set.range r) := by
    refine ⟨S, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa [r] using hupper n
  have hLUB : IsLUB (Set.range r) L := by
    simpa [L] using isLUB_csSup (Set.range_nonempty r) hbdd
  have hlimL : Tendsto r atTop (𝓝 L) :=
    tendsto_atTop_isLUB hmono' hLUB
  have hLpos : 0 < L := by
    have hr0L : r 0 ≤ L := hLUB.1 ⟨0, rfl⟩
    exact (hrpos 0).trans_le hr0L
  have hmBound : ∀ n : ℕ, m n ≤ m 0 * L ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        change m (n + 1) ≤ m 0 * L ^ (n + 1)
        have hrnL : r n ≤ L := hLUB.1 ⟨n, rfl⟩
        have hstep : m (n + 1) ≤ L * m n := by
          apply (div_le_iff₀ (hpos n)).mp
          simpa [r] using hrnL
        calc
          m (n + 1) ≤ L * m n := hstep
          _ ≤ L * (m 0 * L ^ n) :=
            mul_le_mul_of_nonneg_left ih hLpos.le
          _ = m 0 * L ^ (n + 1) := by
            rw [pow_succ]
            ring
  have hxleL : ∀ i : ι, 0 < a i → x i ≤ L := by
    intro i hai
    by_contra hnot
    have hLx : L < x i := lt_of_not_ge hnot
    have hq : 1 < x i / L := by
      rw [lt_div_iff₀ hLpos]
      simpa using hLx
    have hbound : ∀ n : ℕ, a i * (x i / L) ^ n ≤ m 0 := by
      intro n
      have hraw : a i * x i ^ n ≤ m 0 * L ^ n :=
        (hcoord i hai n).trans (hmBound n)
      have hdiv : (a i * x i ^ n) / L ^ n ≤ m 0 := by
        apply (div_le_iff₀ (pow_pos hLpos n)).2
        exact hraw
      calc
        a i * (x i / L) ^ n = (a i * x i ^ n) / L ^ n := by
          rw [div_pow]
          ring
        _ ≤ m 0 := hdiv
    have hpow : Tendsto (fun n : ℕ => (x i / L) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hq
    have hevent := hpow (Ioi_mem_atTop (m 0 / a i))
    change ∀ᶠ n : ℕ in atTop, m 0 / a i < (x i / L) ^ n at hevent
    obtain ⟨n, hn⟩ := hevent.exists
    have hgt : m 0 < a i * (x i / L) ^ n := by
      have hmul := (div_lt_iff₀ hai).mp hn
      simpa [mul_comm] using hmul
    exact (not_lt_of_ge (hbound n)) hgt
  have hSL : S ≤ L := hLeastVisibleUpper L hxleL
  have hLS : L ≤ S := by
    have hSupper : S ∈ upperBounds (Set.range r) := by
      rintro _ ⟨n, rfl⟩
      simpa [r] using hupper n
    exact hLUB.2 hSupper
  have hEq : L = S := le_antisymm hLS hSL
  simpa [r, hEq] using hlimL

/-- Set-theoretic form of
`positiveWeightedMomentRatio_tendsto_of_supremum`: if `S` is the least upper
bound of the visible coordinate values `{x i | a i > 0}`, the successive
moment ratio converges to `S`. -/
theorem positiveWeightedMomentRatio_tendsto_of_isLUB
    {ι : Type u}
    (m : ℕ → ℝ)
    (a x : ι → ℝ)
    (S : ℝ)
    (hpos : ∀ n : ℕ, 0 < m n)
    (hcoord : ∀ i : ι, 0 < a i → ∀ n : ℕ, a i * x i ^ n ≤ m n)
    (hmono : Monotone (fun n : ℕ => m (n + 1) / m n))
    (hupper : ∀ n : ℕ, m (n + 1) / m n ≤ S)
    (hS : IsLUB {y : ℝ | ∃ i : ι, 0 < a i ∧ x i = y} S) :
    Tendsto (fun n : ℕ => m (n + 1) / m n) atTop (𝓝 S) := by
  apply positiveWeightedMomentRatio_tendsto_of_supremum
    m a x S hpos hcoord hmono hupper
  intro b hb
  apply hS.2
  rintro y ⟨i, hai, rfl⟩
  exact hb i hai

/-- `sSup` form of the weighted-moment endpoint principle.  This is the form
used by the spectral specialization: the limit is exactly the supremum of the
coordinates carrying strictly positive state weight. -/
theorem positiveWeightedMomentRatio_tendsto_sSup
    {ι : Type u}
    (m : ℕ → ℝ)
    (a x : ι → ℝ)
    (hpos : ∀ n : ℕ, 0 < m n)
    (hcoord : ∀ i : ι, 0 < a i → ∀ n : ℕ, a i * x i ^ n ≤ m n)
    (hmono : Monotone (fun n : ℕ => m (n + 1) / m n))
    (X : Set ℝ)
    (hX : X = {y : ℝ | ∃ i : ι, 0 < a i ∧ x i = y})
    (hne : X.Nonempty)
    (hbdd : BddAbove X)
    (hupper : ∀ n : ℕ, m (n + 1) / m n ≤ sSup X) :
    Tendsto (fun n : ℕ => m (n + 1) / m n) atTop (𝓝 (sSup X)) := by
  apply positiveWeightedMomentRatio_tendsto_of_isLUB
    m a x (sSup X) hpos hcoord hmono hupper
  rw [← hX]
  exact isLUB_csSup hne hbdd

end

end MathlibAnalytic
end MGAP4D
