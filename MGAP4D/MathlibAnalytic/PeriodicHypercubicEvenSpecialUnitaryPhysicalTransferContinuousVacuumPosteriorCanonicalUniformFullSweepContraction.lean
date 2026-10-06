import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorGenericStrictResolvent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Volume-uniform full-sweep contraction for the actual posterior random scan

PR #5198 factors the posterior random-scan contraction and normalized
resolvent through arbitrary strict bidirectional Dobrushin data.  The
one-link random-scan rate is

  q_H = (n_H - 1 + alpha) / n_H
      = 1 - (1 - alpha) / n_H.

For a fixed H this is strictly below one, but q_H approaches one as the number
n_H of spatial links grows.  This file changes the unit of time from one
single-link update to one complete random-scan sweep of n_H updates.

Using the elementary inequality

  1 - x <= exp(-x),

we obtain

  q_H ^ n_H <= exp(-(1 - alpha)).

The right side no longer contains H.  Iterating complete sweeps therefore gives

  U^(m n_H) v
    <= exp(-(1-alpha))^m V

for every nonnegative pointwise envelope v <= V.

Specializing alpha to the actual canonical coefficient from PRs #5195--#5197
produces one H- and N-independent full-sweep contraction factor on the positive
uniform Dobrushin interval of PR #5196.

This is a Markov-update sweep statement.  It does not identify one sweep with
one Euclidean physical-time step, prove spacing-scaled generator convergence,
close H1-D5 exact descent, or prove the complete four-dimensional Yang--Mills
mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance posteriorUniformFullSweepSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The H-independent exponential rate associated with one complete sweep of
arbitrary strict posterior Dobrushin data. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) : ℝ :=
  Real.exp (-(1 - D.coefficient))

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate_pos
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    0 <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
        D := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
  exact Real.exp_pos _

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate_lt_one
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
        D < 1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
  rw [Real.exp_lt_one_iff]
  linarith [D.coefficient_lt_one]

/-- The one-link random-scan rate is exactly one minus the Dobrushin gap
divided by the finite spatial-link count. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_eq_one_sub_gap_div_card
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
        D =
      1 -
        (1 - D.coefficient) /
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
  dsimp only
  change
    (n - 1 + D.coefficient) / n =
      1 - (1 - D.coefficient) / n
  field_simp [hnNe] <;> ring

/-- Raising the one-link random-scan rate to one complete sweep removes the
finite-volume cardinality from the contraction bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_pow_card_le_fullSweepRate
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
        D) ^
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
        D := by
  let nNat : ℕ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let n : ℝ := nNat
  let gap : ℝ := 1 - D.coefficient
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  have hnNatPos : 0 < nNat := by
    dsimp [nNat]
    exact periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hnPos : 0 < n := Nat.cast_pos.mpr hnNatPos
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hGapPos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr D.coefficient_lt_one
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_nonneg
        D
  have hqEq : q = 1 - gap / n := by
    dsimp [q, gap, n, nNat]
    rw [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_eq_one_sub_gap_div_card
        D]
  have hBase :
      q ≤ Real.exp (-(gap / n)) := by
    rw [hqEq]
    exact Real.one_sub_le_exp_neg (gap / n)
  have hPow :
      q ^ nNat ≤ (Real.exp (-(gap / n))) ^ nNat :=
    pow_le_pow_left₀ hqNonneg hBase nNat
  calc
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
        D) ^
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) =
      q ^ nNat := by rfl
    _ ≤ (Real.exp (-(gap / n))) ^ nNat := hPow
    _ = Real.exp (-gap) := by
      rw [← Real.exp_nat_mul]
      congr 1
      change (nNat : ℝ) * (-(gap / n)) = -gap
      dsimp [n]
      field_simp [hnNe]
    _ =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
        D := by
      rfl

/-- Every m complete random-scan sweeps contract a nonnegative pointwise
variation envelope at the H-independent full-sweep rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationIterate_fullSweep_le
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (m : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation
        (m * Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
        source ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
        D) ^ m * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  let rho :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
      D
  let nNat : ℕ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_nonneg
        D
  have hBlock :
      q ^ nNat ≤ rho := by
    simpa [q, rho, nNat] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_pow_card_le_fullSweepRate
        D
  have hBlockPow :
      (q ^ nNat) ^ m ≤ rho ^ m :=
    pow_le_pow_left₀ (pow_nonneg hqNonneg nNat) hBlock m
  have hIter :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationIterate_le_rate_pow_mul
      D hColumn variation hVariationNonneg V hV hVariationLe
      (m * nNat) source
  calc
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation (m * nNat) source ≤
      q ^ (m * nNat) * V := by
        simpa [q, nNat] using hIter
    _ = (q ^ nNat) ^ m * V := by
      rw [Nat.mul_comm m nNat, pow_mul]
    _ ≤ rho ^ m * V :=
      mul_le_mul_of_nonneg_right hBlockPow hV
    _ =
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate
        D) ^ m * V := by
      rfl

/-- H- and N-independent full-sweep rate for the actual canonical posterior
coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
    (s beta : ℝ) : ℝ :=
  Real.exp
    (-(1 -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta))

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_pos
    (s beta : ℝ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  exact Real.exp_pos _

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_lt_one
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s beta < 1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  rw [Real.exp_lt_one_iff]
  have hAlpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
      s hs beta hbeta hbetaCutoff
  linarith

/-- The canonical one-link random-scan rate raised to one complete sweep is
bounded by the same H-independent scalar for every finite H and N. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_pow_card_le_fullSweepRate
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    let D :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
        H N hN s hs beta hbeta hbetaCutoff B
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
        D) ^
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s beta := by
  dsimp only
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B
  have h :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_pow_card_le_fullSweepRate
      D
  simpa [
    D,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  ] using h

/-- Canonical actual posterior variation contracts geometrically per complete
sweep with a rate independent of H and N. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_fullSweep_le
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (m : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          H N hN s hs beta hbeta hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation
        (m * Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
        source ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s beta) ^ m * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B
  have hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient := by
    intro source
    simpa [D] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_columnSum_le_coefficient
        H N hN s hs beta hbeta hbetaCutoff B source
  have h :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationIterate_fullSweep_le
      D hColumn variation hVariationNonneg V hV hVariationLe m source
  simpa [
    D,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinFullSweepRate,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  ] using h

/-- Powers of the canonical full-sweep rate converge to zero uniformly in the
finite-volume parameters because the rate itself contains no H or N. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_pow_tendsto_zero
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    Tendsto
      (fun m : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s beta) ^ m)
      atTop
      (nhds 0) := by
  exact
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_pos
        s beta).le
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_lt_one
        s hs beta hbeta hbetaCutoff)

end

end MathlibAnalytic
end MGAP4D
