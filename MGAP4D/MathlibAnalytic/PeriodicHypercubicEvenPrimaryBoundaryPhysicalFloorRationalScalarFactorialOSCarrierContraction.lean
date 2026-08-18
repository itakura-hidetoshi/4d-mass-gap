import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarOSObservableUniformNormBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Factorial OS carrier contraction

The canonical same-root construction now provides two ingredients for every fixed-slot bounded
continuous observable `F` and every nonnegative rational shift `t`:

* the midpoint estimate `‖T_t F‖² ≤ ‖F‖ * ‖T_{2t} F‖`;
* the shift-independent far-time bound `‖T_s F‖ ≤ ‖F.observable‖∞`.

This file closes the standard dyadic Osterwalder--Schrader argument.  If `‖T_t F‖` were strictly
larger than `‖F‖`, the midpoint estimate at the dyadic times `2^n t` would force at least doubly
exponential growth.  Mathlib's `tendsto_pow_atTop_atTop_of_one_lt` then contradicts the uniform
far-time bound.  The zero-seminorm case is handled directly by the same recurrence.

The result is the genuine same-root fixed-slot contraction

`‖T_t F‖ ≤ ‖F‖`.

No Hilbert-completion extension, direct-limit operator, semigroup, Hamiltonian, spectral statement,
or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A nonnegative sequence with the OS midpoint recursion
`a_n² ≤ base * a_{n+1}` and a uniform upper bound cannot start above `base`.

This elementary real lemma isolates the only Archimedean step in the dyadic contraction argument. -/
theorem first_le_base_of_sq_le_base_mul_next_of_uniformBound
    (base M : ℝ)
    (a : ℕ → ℝ)
    (hbase : 0 ≤ base)
    (ha : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a n ^ 2 ≤ base * a (n + 1))
    (hbound : ∀ n, a n ≤ M) :
    a 0 ≤ base := by
  by_cases hbase0 : base = 0
  · subst base
    have h := hrec 0
    have ha0 := ha 0
    nlinarith [sq_nonneg (a 0)]
  · have hbase_pos : 0 < base :=
      lt_of_le_of_ne hbase (Ne.symm hbase0)
    by_contra hnot
    have hstrict : base < a 0 := lt_of_not_ge hnot
    let r : ℝ := a 0 / base
    have hr : 1 < r := by
      dsimp [r]
      exact (lt_div_iff₀ hbase_pos).2 (by simpa using hstrict)
    have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr.le
    have hbase_mul_r : base * r = a 0 := by
      dsimp [r]
      calc
        base * (a 0 / base) = (a 0 / base) * base := mul_comm _ _
        _ = a 0 := div_mul_cancel₀ _ hbase0
    have hlower : ∀ n : ℕ, base * r ^ (2 ^ n) ≤ a n := by
      intro n
      induction n with
      | zero =>
          simpa [hbase_mul_r] using (le_refl (a 0))
      | succ n ih =>
          have hnonneg : 0 ≤ base * r ^ (2 ^ n) :=
            mul_nonneg hbase (pow_nonneg hr_nonneg _)
          have hsquare :
              (base * r ^ (2 ^ n)) ^ 2 ≤ (a n) ^ 2 := by
            simpa [pow_two] using mul_self_le_mul_self hnonneg ih
          have hchain :
              (base * r ^ (2 ^ n)) ^ 2 ≤ base * a (n + 1) :=
            hsquare.trans (hrec n)
          have hscaled :
              base * (base * (r ^ (2 ^ n)) ^ 2) ≤ base * a (n + 1) := by
            calc
              base * (base * (r ^ (2 ^ n)) ^ 2) =
                  (base * r ^ (2 ^ n)) ^ 2 := by ring
              _ ≤ base * a (n + 1) := hchain
          have hcancel :
              base * (r ^ (2 ^ n)) ^ 2 ≤ a (n + 1) := by
            nlinarith [hscaled]
          calc
            base * r ^ (2 ^ (n + 1)) =
                base * (r ^ (2 ^ n)) ^ 2 := by
              rw [Nat.pow_succ, pow_mul]
            _ ≤ a (n + 1) := hcancel
    have hrpow : Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hr
    have htwo : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by norm_num)
    have hdyadic : Tendsto (fun n : ℕ => r ^ (2 ^ n)) atTop atTop :=
      hrpow.comp htwo
    have hscaled_atTop :
        Tendsto (fun n : ℕ => base * r ^ (2 ^ n)) atTop atTop :=
      hdyadic.const_mul_atTop hbase_pos
    have hlarge :
        ∀ᶠ n : ℕ in atTop, M + 1 ≤ base * r ^ (2 ^ n) :=
      (tendsto_atTop.1 hscaled_atTop) (M + 1)
    rcases eventually_atTop.1 hlarge with ⟨n0, hn0⟩
    have hn := hn0 n0 (le_refl n0)
    have hlo := hlower n0
    have hup := hbound n0
    nlinarith

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Nonnegative rational time translation is a contraction on the canonical factorial fixed-slot OS
seminormed carrier. -/
theorem fixedSlotCarrierTimeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ≤ ‖F‖ := by
  have hshift_nonneg : ∀ n : ℕ, 0 ≤ ((2 : ℚ) ^ n) * t := by
    intro n
    exact mul_nonneg (pow_nonneg (by norm_num) _) ht
  have hnorm_time_congr :
      ∀ {s u : ℚ} (hs : 0 ≤ s) (hu : 0 ≤ u), s = u →
        ‖P.fixedSlotCarrierTimeTranslate s hs F‖ =
          ‖P.fixedSlotCarrierTimeTranslate u hu F‖ := by
    intro s u hs hu hsu
    subst u
    rfl
  let a : ℕ → ℝ := fun n =>
    ‖P.fixedSlotCarrierTimeTranslate
      (((2 : ℚ) ^ n) * t) (hshift_nonneg n) F‖
  have ha : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    exact norm_nonneg _
  have hrec : ∀ n : ℕ, a n ^ 2 ≤ ‖F‖ * a (n + 1) := by
    intro n
    have hmid :=
      P.fixedSlotCarrierTimeTranslate_norm_sq_le_mul_norm_double
        (((2 : ℚ) ^ n) * t) (hshift_nonneg n) F
    have htime :
        (((2 : ℚ) ^ n) * t) + (((2 : ℚ) ^ n) * t) =
          ((2 : ℚ) ^ (n + 1)) * t := by
      rw [pow_succ]
      ring
    have hnorm_double :=
      hnorm_time_congr
        (add_nonneg (hshift_nonneg n) (hshift_nonneg n))
        (hshift_nonneg (n + 1)) htime
    rw [hnorm_double] at hmid
    simpa [a] using hmid
  have hbound : ∀ n : ℕ, a n ≤ ‖F.observable‖ := by
    intro n
    exact
      P.fixedSlotCarrierTimeTranslate_norm_le_observable_norm
        (((2 : ℚ) ^ n) * t) (hshift_nonneg n) F
  have hfirst : a 0 ≤ ‖F‖ :=
    first_le_base_of_sq_le_base_mul_next_of_uniformBound
      ‖F‖ ‖F.observable‖ a (norm_nonneg F) ha hrec hbound
  change
    ‖P.fixedSlotCarrierTimeTranslate
      (((2 : ℚ) ^ 0) * t) (hshift_nonneg 0) F‖ ≤ ‖F‖ at hfirst
  have hzero : ((2 : ℚ) ^ 0) * t = t := by norm_num
  have hnorm_zero := hnorm_time_congr (hshift_nonneg 0) ht hzero
  rw [hnorm_zero] at hfirst
  exact hfirst

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
