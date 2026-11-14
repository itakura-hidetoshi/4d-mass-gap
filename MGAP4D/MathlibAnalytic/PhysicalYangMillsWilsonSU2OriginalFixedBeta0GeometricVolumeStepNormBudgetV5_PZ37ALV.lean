import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0VolumeStepLossBudgetV5_PZ37ALU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALV — geometric volume-step scalar norm budget at original beta0

The original, unchanged physical SU(2) Wilson transfer restrictions R_H(beta0)
live on H-dependent full-top-orthogonal Hilbert spaces. No difference of
operators or vectors belonging to distinct H is used.

This leaf identifies the ALU actual one-step downward deficit loss exactly
with the positive part of the INCREASE of the true scalar squared excited
operator norm n_H = ||R_H(beta0)||^2:
  L_H = max(n_(H+1) - n_H, 0).

A physically meaningful but NOT YET PROVED finite-size mixing criterion is
  n_(H+1) <= n_H + C*r^H,
  C >= 0, 0 <= r < 1, C < (1-r)*delta_0.
Its geometric summation gives an original-beta0 uniform gap, strictly
conditioned on this direct Wilson-model one-step norm estimate.

A second, weaker-in-scope route requires exponential step control only after
any fixed finite prefix M, with C < (1-r)*delta_M. The prefix is certified
by ALT without additional premises.

Neither geometric hypothesis is asserted for the original Wilson model.
In particular, neither theorem establishes the all-H fixed-beta0 gap
unconditionally, nor the continuum Yang-Mills mass gap. This is an append-only
Lean leaf with unchanged original physics, fixed coupling, pinned dependencies,
public import roots and earlier certified sources.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace GroundStatePosteriorJoint

local notation "D" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
local notation "Gap" => p4Q2PZ37ALT_originalFixedGapAt
local notation "L" => p4Q2PZ37ALU_originalFixedOneStepDownwardLoss

/-- Squared norm of the actual original fixed-beta0 Wilson normalized
full-top-orthogonal restriction. This is a REAL scalar for each H, even
though the operators have different H-dependent carrier spaces. -/
noncomputable def p4Q2PZ37ALV_originalFixedExcitedNormSq (H : ℕ) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le‖ ^ 2

theorem p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq (H : ℕ) :
    D H = 1 - p4Q2PZ37ALV_originalFixedExcitedNormSq H := by
  rfl

/-- An exact representation of ALU's smallest possible nonnegative
one-step loss using only the genuine physical scalar squared norms. -/
theorem p4Q2PZ37ALV_oneStepLoss_eq_positive_normSqIncrease (H : ℕ) :
    L H =
      max (p4Q2PZ37ALV_originalFixedExcitedNormSq (H + 1) -
        p4Q2PZ37ALV_originalFixedExcitedNormSq H) 0 := by
  unfold p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
  rw [p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq H,
    p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq (H + 1)]
  congr 1
  ring

/-- A bound on the scalar squared physical excited-norm increment
is a bound on the ACTUAL ALU deficit loss. The Hilbert operators themselves
are never subtracted across volumes. -/
theorem p4Q2PZ37ALV_oneStepLoss_le_of_normSqIncrease
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hstep : p4Q2PZ37ALV_originalFixedExcitedNormSq (H + 1) ≤
      p4Q2PZ37ALV_originalFixedExcitedNormSq H + b) :
    L H ≤ b := by
  rw [p4Q2PZ37ALV_oneStepLoss_eq_positive_normSqIncrease]
  apply max_le
  · linarith
  · exact hb

/-- Polynomial geometric finite-sum identity; no analytic infinite series
or external mixing theorem is used. -/
theorem p4Q2PZ37ALV_geometricFiniteSum_identity
    (C r : ℝ) (H : ℕ) :
    (1 - r) * (Finset.range H).sum (fun i : ℕ => C * r ^ i) =
      C * (1 - r ^ H) := by
  induction H with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (1 - r) * ((Finset.range n).sum (fun i : ℕ => C * r ^ i) +
            C * r ^ n) =
          (1 - r) * (Finset.range n).sum (fun i : ℕ => C * r ^ i) +
            (1 - r) * (C * r ^ n) := by ring
        _ = C * (1 - r ^ n) + (1 - r) * (C * r ^ n) := by rw [ih]
        _ = C * (1 - r ^ (n + 1)) := by rw [pow_succ]; ring

/-- Uniform finite geometric budget from 0<=r<1; this is an algebraic
summation statement, not an assertion about Wilson finite-size mixing. -/
theorem p4Q2PZ37ALV_geometricFiniteSum_le
    (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (H : ℕ) :
    (Finset.range H).sum (fun i : ℕ => C * r ^ i) ≤ C / (1 - r) := by
  have hEq := p4Q2PZ37ALV_geometricFiniteSum_identity C r H
  have hScaled :
      (1 - r) * (Finset.range H).sum (fun i : ℕ => C * r ^ i) ≤ C := by
    rw [hEq]
    nlinarith only [mul_nonneg hC (pow_nonneg hr0 H)]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  nlinarith only [hScaled]

/-- Quantitative ALL-VOLUME original-beta0 Wilson criterion. The independent
physical input is the genuine cross-volume scalar excited-norm estimate
  n_(H+1) <= n_H + C*r^H.
No such estimate is proved by this theorem. -/
theorem p4Q2PZ37ALV_uniformGap_of_global_geometricNormSqStep
    (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hSmall : C < (1 - r) * D 0)
    (hSteps : ∀ H : ℕ,
      p4Q2PZ37ALV_originalFixedExcitedNormSq (H + 1) ≤
        p4Q2PZ37ALV_originalFixedExcitedNormSq H + C * r ^ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  let b : ℕ → ℝ := fun H => C * r ^ H
  have hb : ∀ H : ℕ, 0 ≤ b H := by
    intro H
    exact mul_nonneg hC (pow_nonneg hr0 H)
  have hstep : ∀ H : ℕ, D H ≤ D (H + 1) + b H := by
    intro H
    have hs : p4Q2PZ37ALV_originalFixedExcitedNormSq (H + 1) ≤
        p4Q2PZ37ALV_originalFixedExcitedNormSq H + b H := by
      simpa [b] using hSteps H
    have hl := p4Q2PZ37ALV_oneStepLoss_le_of_normSqIncrease H (b H) (hb H) hs
    have hd := p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_controlsDeficit H
    linarith
  have htotal : ∀ H : ℕ, (Finset.range H).sum b ≤ C / (1 - r) := by
    intro H
    simpa [b] using p4Q2PZ37ALV_geometricFiniteSum_le C r hC hr0 hr1 H
  have hbound : C / (1 - r) < D 0 := by
    apply (div_lt_iff₀ (sub_pos.mpr hr1)).2
    calc
      C < (1 - r) * D 0 := hSmall
      _ = D 0 * (1 - r) := by ring
  exact p4Q2PZ37ALU_originalFixedUniformGap_of_stepwiseBudget
    b (C / (1 - r)) hb hstep htotal hbound

/-- An exponentially small scalar norm increase is required ONLY on the
tail beginning at M. The first M physical volumes retain ALT's exact,
unconditional positive finite-prefix certificate.

The unproved physical tail hypothesis and its strict threshold at delta_M
remain explicit; this is not an unconditional Wilson mass gap. -/
theorem p4Q2PZ37ALV_uniformGap_of_tail_geometricNormSqStep
    (M : ℕ) (C r : ℝ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hSmall : C < (1 - r) * D M)
    (hSteps : ∀ n : ℕ,
      p4Q2PZ37ALV_originalFixedExcitedNormSq (M + n + 1) ≤
        p4Q2PZ37ALV_originalFixedExcitedNormSq (M + n) + C * r ^ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have hstep : ∀ n : ℕ,
      D (M + n) ≤ D (M + n + 1) + C * r ^ n := by
    intro n
    have hs := hSteps n
    rw [p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq (M + n),
      p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq (M + n + 1)]
    linarith
  have htel : ∀ n : ℕ,
      D M ≤ D (M + n) +
        (Finset.range n).sum (fun i : ℕ => C * r ^ i) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hs := hstep n
        have hidx : M + (n + 1) = M + n + 1 := by omega
        rw [hidx, Finset.sum_range_succ]
        linarith
  have htailBound : C / (1 - r) < D M := by
    apply (div_lt_iff₀ (sub_pos.mpr hr1)).2
    calc
      C < (1 - r) * D M := hSmall
      _ = D M * (1 - r) := by ring
  obtain ⟨εprefix, hprefixPos, hprefix⟩ :=
    p4Q2PZ37ALT_originalFixedFinitePrefixUniformGap M
  let εtail : ℝ := (D M - C / (1 - r)) / 2
  have htailPos : 0 < εtail := by
    dsimp [εtail]
    linarith
  refine ⟨min εprefix εtail, lt_min hprefixPos htailPos, ?_⟩
  intro H
  by_cases hHM : H ≤ M
  · exact (min_le_left _ _).trans (hprefix H hHM)
  · let n : ℕ := H - M
    have hidx : M + n = H := by dsimp [n]; omega
    have ht := htel n
    rw [hidx] at ht
    have hs := p4Q2PZ37ALV_geometricFiniteSum_le C r hC hr0 hr1 n
    have hg := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
    have hmin : min εprefix εtail ≤ εtail := min_le_right _ _
    dsimp [εtail] at hmin
    linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_originalFixedExcitedNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_oneStepLoss_eq_positive_normSqIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_oneStepLoss_le_of_normSqIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_geometricFiniteSum_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_geometricFiniteSum_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_uniformGap_of_global_geometricNormSqStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALV_uniformGap_of_tail_geometricNormSqStep
