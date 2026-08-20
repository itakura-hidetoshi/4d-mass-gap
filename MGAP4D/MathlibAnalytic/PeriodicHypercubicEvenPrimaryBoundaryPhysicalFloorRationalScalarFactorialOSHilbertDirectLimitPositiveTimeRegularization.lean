import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularCorrelationCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitSymmetricPositive
import Mathlib.Tactic

/-!
# Positive-time regularization of the factorial OS rational semigroup

The canonical same-root factorial OS semigroup was deliberately constructed without assuming
strong continuity at zero on the whole completed direct-limit Hilbert space.  The preceding layer
characterized the regular sector by a scalar self-correlation limit.  Here we prove a stronger
structural fact: **every strictly positive rational-time translate is automatically regular**.

The argument is completely internal to the already-constructed symmetric positive contraction
semigroup.  For a fixed rational step `d`, set

`a_k = ‖T_(k d) x‖²`.

The OS midpoint factorization gives the discrete convexity identity

`a_k - 2 a_(k+1) + a_(k+2)
   = ‖T_(k d) x - T_((k+2)d) x‖² ≥ 0`.

Hence the decrements `a_k-a_(k+1)` decrease with `k`.  Averaging the first `2n` decrements yields a
quantitative bound at every positive time `s`:

`‖T_t(T_s x) - T_s x‖² ≤ ‖x‖² / n`

whenever `0 ≤ t ≤ s/n`.  Letting `n → ∞` proves zero-time strong continuity of the orbit starting
from `T_s x`.

Thus `range(T_s)` is contained in the canonical regular sector for every `s > 0`.  This is an
operator-theoretic same-root regularization theorem; no stochastic-continuity hypothesis, spectral
functional calculus, mass-gap assumption, or old-carrier identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

noncomputable section

/-- For a real sequence with nonnegative discrete second differences, the `n`-th decrement is
bounded by the average total drop over the first `n` steps. -/
theorem natCast_mul_decrement_le_totalDrop_of_discreteConvex
    (a : ℕ → ℝ)
    (hconv : ∀ k : ℕ, 0 ≤ a k - 2 * a (k + 1) + a (k + 2)) :
    ∀ n : ℕ, (n : ℝ) * (a n - a (n + 1)) ≤ a 0 - a n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hdec : a (n + 1) - a (n + 2) ≤ a n - a (n + 1) := by
        have h := hconv n
        linarith
      have hmul :
          (n : ℝ) * (a (n + 1) - a (n + 2)) ≤
            (n : ℝ) * (a n - a (n + 1)) :=
        mul_le_mul_of_nonneg_left hdec (Nat.cast_nonneg n)
      calc
        ((n + 1 : ℕ) : ℝ) * (a (n + 1) - a (n + 2)) =
            (n : ℝ) * (a (n + 1) - a (n + 2)) +
              (a (n + 1) - a (n + 2)) := by
          push_cast
          ring
        _ ≤ (n : ℝ) * (a n - a (n + 1)) +
              (a n - a (n + 1)) :=
          add_le_add hmul hdec
        _ ≤ (a 0 - a n) + (a n - a (n + 1)) :=
          add_le_add_right ih _
        _ = a 0 - a (n + 1) := by ring

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The norm of a completed direct-limit orbit is antitone in nonnegative rational time. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    Antitone
      (fun t : NNRat =>
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x‖) := by
  intro s t hst
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  rw [← P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add u s x]
  exact
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le u
      (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x)

/-- Along every fixed rational time mesh, the squared orbit norm has nonnegative discrete second
difference.  This is the OS factorization written as an elementary convexity identity. -/
theorem fixedSlotHilbertDirectLimitNNRatOrbitNormSq_discreteConvex
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (d : NNRat)
    (x : P.fixedSlotHilbertDirectLimitCompletion)
    (k : ℕ) :
    0 ≤
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM ((k : NNRat) * d) x‖ ^ 2 -
        2 *
          ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
            (((k + 1 : ℕ) : NNRat) * d) x‖ ^ 2 +
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k + 2 : ℕ) : NNRat) * d) x‖ ^ 2 := by
  let z : P.fixedSlotHilbertDirectLimitCompletion :=
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM ((k : NNRat) * d) x
  have h1 :
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d z =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k + 1 : ℕ) : NNRat) * d) x := by
    dsimp [z]
    calc
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM ((k : NNRat) * d) x) =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k : NNRat) * d) + d) x :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add d ((k : NNRat) * d) x
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k + 1 : ℕ) : NNRat) * d) x := by
        congr 1
        push_cast
        ring
  have h2 :
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d) z =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k + 2 : ℕ) : NNRat) * d) x := by
    dsimp [z]
    calc
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d)
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM ((k : NNRat) * d) x) =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k : NNRat) * d) + (d + d)) x :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add (d + d) ((k : NNRat) * d) x
      _ = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (((k + 2 : ℕ) : NNRat) * d) x := by
        congr 1
        push_cast
        ring
  have hfacQ :=
    P.fixedSlotHilbertDirectLimitTimeTranslate_inner_factorization
      (d : ℚ) d.2 z z
  have hfac :
      inner ℝ
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d z)
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d z) =
        inner ℝ z
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d) z) := by
    simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using hfacQ
  have hmid :
      inner ℝ z
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d) z) =
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d z‖ ^ 2 := by
    rw [← hfac, real_inner_self_eq_norm_sq]
  have hnonneg :
      0 ≤ ‖z‖ ^ 2 -
        2 * ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d z‖ ^ 2 +
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d) z‖ ^ 2 := by
    calc
      0 ≤ ‖z - P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d) z‖ ^ 2 :=
        sq_nonneg _
      _ = ‖z‖ ^ 2 -
          2 * ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM d z‖ ^ 2 +
          ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (d + d) z‖ ^ 2 := by
        rw [norm_sub_sq_real, hmid]
  dsimp [z] at hnonneg
  rw [h1, h2] at hnonneg
  exact hnonneg

/-- Quantitative positive-time smoothing.  If `s>0`, then every sufficiently small rational step
`t ≤ s/n` moves the positive-time vector `T_s x` by at most `‖x‖/√n` in the squared-norm sense. -/
theorem fixedSlotHilbertDirectLimitNNRat_positiveTime_sub_norm_sq_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (x : P.fixedSlotHilbertDirectLimitCompletion)
    (n : ℕ) (hn : 0 < n)
    (t : NNRat)
    (ht : t ≤ s / (n : NNRat)) :
    ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x) -
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x‖ ^ 2 ≤
      ‖x‖ ^ 2 / (n : ℝ) := by
  let den : NNRat := ((2 * n : ℕ) : NNRat)
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  let d : NNRat := s / den
  have hd_pos : 0 < d := div_pos hs hden_pos
  have hmesh : den * d = s := by
    dsimp [d]
    exact mul_div_cancel₀ s hden_ne
  let a : ℕ → ℝ := fun k =>
    ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM ((k : NNRat) * d) x‖ ^ 2
  have hconv : ∀ k : ℕ, 0 ≤ a k - 2 * a (k + 1) + a (k + 2) := by
    intro k
    exact P.fixedSlotHilbertDirectLimitNNRatOrbitNormSq_discreteConvex d x k
  have havg := natCast_mul_decrement_le_totalDrop_of_discreteConvex a hconv (2 * n)
  have htime2n : (((2 * n : ℕ) : NNRat) * d) = s := by
    change den * d = s
    exact hmesh
  have htime2n1 : ((((2 * n + 1 : ℕ) : NNRat) * d)) = s + d := by
    calc
      (((2 * n + 1 : ℕ) : NNRat) * d) = den * d + d := by
        dsimp [den]
        push_cast
        ring
      _ = s + d := by rw [hmesh]
  have ha0 : a 0 = ‖x‖ ^ 2 := by
    dsimp [a]
    simp [P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_zero]
  have ha2n :
      a (2 * n) =
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x‖ ^ 2 := by
    dsimp [a]
    rw [htime2n]
  have ha2n1 :
      a (2 * n + 1) =
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + d) x‖ ^ 2 := by
    dsimp [a]
    rw [htime2n1]
  have hdrop_nonneg : 0 ≤ a (2 * n) := by
    dsimp [a]
    positivity
  have hchain :
      ((2 * n : ℕ) : ℝ) * (a (2 * n) - a (2 * n + 1)) ≤ ‖x‖ ^ 2 := by
    calc
      ((2 * n : ℕ) : ℝ) * (a (2 * n) - a (2 * n + 1)) ≤
          a 0 - a (2 * n) := havg
      _ ≤ a 0 := by linarith
      _ = ‖x‖ ^ 2 := ha0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdenR : 0 < (2 : ℝ) * (n : ℝ) := mul_pos (by norm_num) hnR
  have hlate :
      a (2 * n) - a (2 * n + 1) ≤
        ‖x‖ ^ 2 / ((2 : ℝ) * (n : ℝ)) := by
    apply (le_div_iff₀ hdenR).2
    simpa [Nat.cast_mul] using hchain
  let y : P.fixedSlotHilbertDirectLimitCompletion :=
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x
  have ht_half : t / 2 ≤ d := by
    calc
      t / 2 ≤ (s / (n : NNRat)) / 2 := by gcongr
      _ = d := by
        dsimp [d, den]
        field_simp
        <;> ring
  have horbit :
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t / 2) y =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + t / 2) x := by
    dsimp [y]
    calc
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t / 2)
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x) =
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + t / 2) x :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_add (t / 2) s x
  have hnorm_mono :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + d) x‖ ≤
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + t / 2) x‖ := by
    exact
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_antitone x
        (add_le_add_left ht_half s)
  have hnorm_sq_mono :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + d) x‖ ^ 2 ≤
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + t / 2) x‖ ^ 2 := by
    nlinarith [norm_nonneg
      (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + d) x),
      norm_nonneg
      (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (s + t / 2) x)]
  have hcorrQ :=
    P.fixedSlotHilbertDirectLimitTimeTranslate_inner_self_eq_half_norm_sq
      (t : ℚ) t.2 y
  have hcorr :
      inner ℝ y (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t y) =
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM (t / 2) y‖ ^ 2 := by
    simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using hcorrQ
  have hcorr_lower :
      a (2 * n + 1) ≤
        inner ℝ y (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t y) := by
    rw [hcorr, horbit, ha2n1]
    exact hnorm_sq_mono
  have hy_norm : ‖y‖ ^ 2 = a (2 * n) := by
    rw [ha2n]
    rfl
  have hdefect :
      ‖y‖ ^ 2 - inner ℝ y (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t y) ≤
        a (2 * n) - a (2 * n + 1) := by
    rw [hy_norm]
    linarith
  have hstrong :=
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_sub_norm_sq_le_twice_correlation_defect
      t y
  calc
    ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t y - y‖ ^ 2 ≤
        2 *
          (‖y‖ ^ 2 -
            inner ℝ y (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t y)) := hstrong
    _ ≤ 2 * (a (2 * n) - a (2 * n + 1)) := by gcongr
    _ ≤ 2 * (‖x‖ ^ 2 / ((2 : ℝ) * (n : ℝ))) := by gcongr
    _ = ‖x‖ ^ 2 / (n : ℝ) := by field_simp [hnR.ne']; ring

/-- Every strictly positive nonnegative-rational translate of an arbitrary completed direct-limit
vector belongs to the canonical zero-time regular sector. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_mem_regularSubspace_of_pos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x ∈
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  rw [P.mem_fixedSlotHilbertDirectLimitRegularSubspace_iff]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεsq : 0 < ε ^ 2 := by positivity
  obtain ⟨n, hnlarge⟩ := exists_nat_gt (‖x‖ ^ 2 / ε ^ 2)
  have hquot_nonneg : 0 ≤ ‖x‖ ^ 2 / ε ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnR : 0 < (n : ℝ) := lt_of_le_of_lt hquot_nonneg hnlarge
  have hn : 0 < n := by exact_mod_cast hnR
  have hmul : ‖x‖ ^ 2 < (n : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ hεsq).1 hnlarge
  have hratio : ‖x‖ ^ 2 / (n : ℝ) < ε ^ 2 := by
    exact (div_lt_iff₀ hnR).2 (by simpa [mul_comm] using hmul)
  let δ : NNRat := s / (n : NNRat)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hs (by exact_mod_cast hn)
  filter_upwards [Iio_mem_nhds hδ] with t ht
  have ht_le : t ≤ s / (n : NNRat) := le_of_lt ht
  have hbound :=
    P.fixedSlotHilbertDirectLimitNNRat_positiveTime_sub_norm_sq_le
      s hs x n hn t ht_le
  have hsq :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x) -
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt hbound hratio
  have habs :
      |‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x) -
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x‖| < ε :=
    abs_lt_of_sq_lt_sq hsq (le_of_lt hε)
  have hnorm :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x) -
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x‖ < ε := by
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  simpa [dist_eq_norm] using hnorm

/-- The range of every strictly positive rational-time contraction lies in the canonical regular
sector. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_range_le_regularSubspace_of_pos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s) :
    LinearMap.range
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s).toLinearMap ≤
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_mem_regularSubspace_of_pos s hs x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
