import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFullSweepGeneratorScaling
import Mathlib.Tactic

/-!
# Fixed posterior full-sweep gap forces infinite spacing-scaled mass rate

PR #5202 isolates the finite-mass generator-scaling requirement

  (1 - alpha_bar(s,beta_n)) / a_n -> m > 0.

This file proves the complementary no-go statement.  If beta is fixed inside
the strict volume-uniform Dobrushin interval, then

  delta = 1 - alpha_bar(s,beta) > 0

is a fixed positive number.  For every positive lattice-spacing sequence
a_n -> 0,

  delta / a_n -> +infinity.

Using the exact logarithmic identity from PR #5202, the same is true for the
derived full-sweep mass rate

  -log rho(s,beta) / a_n.

Thus a fixed positive posterior sweep gap cannot produce a finite continuum
mass when one sweep is assigned a time scale tending to zero.  A finite mass
requires either a scale-dependent coupling beta_n making the gap of order a_n,
or a different theorem identifying the physical duration of one sweep.

This is a precise obstruction theorem, not a physical-time identification.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

/-- A fixed positive numerator divided by a positive sequence tending to zero
diverges to positive infinity. -/
theorem positive_const_div_tendsto_atTop_of_pos_tendsto_zero
    (a : ℕ → ℝ)
    (haPos : ∀ n, 0 < a n)
    (haZero : Tendsto a atTop (nhds 0))
    (delta : ℝ)
    (hDelta : 0 < delta) :
    Tendsto (fun n => delta / a n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  let c : ℝ := max b 1
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  let epsilon : ℝ := delta / c
  have hEpsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos hDelta hcPos
  have hEventually :
      ∀ᶠ n in atTop, a n < epsilon :=
    (tendsto_order.1 haZero).2 epsilon hEpsilon
  filter_upwards [hEventually] with n hn
  have hmul :
      c * a n < delta := by
    calc
      c * a n < c * epsilon :=
        mul_lt_mul_of_pos_left hn hcPos
      _ = delta := by
        dsimp [epsilon]
        field_simp [ne_of_gt hcPos]
  have hdiv : c < delta / a n :=
    (lt_div_iff₀ (haPos n)).2 hmul
  exact (le_max_left b 1).trans hdiv.le

/-- For fixed coupling inside the canonical positive Dobrushin interval, the
spacing-scaled posterior full-sweep Dobrushin gap diverges to infinity as
positive lattice spacing tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformGap_div_spacing_tendsto_atTop
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta) /
          latticeSpacing n)
      atTop atTop := by
  have hGap :
      0 <
        1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta := by
    exact sub_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
        s hs beta hbeta hbetaCutoff)
  exact
    positive_const_div_tendsto_atTop_of_pos_tendsto_zero
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta)
      hGap

/-- Equivalently, the exact logarithmic mass rate of the fixed-coupling
posterior full-sweep factor diverges to infinity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_fixedBeta_massRate_tendsto_atTop
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0)) :
    Tendsto
      (fun n =>
        -Real.log
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
              s beta) /
          latticeSpacing n)
      atTop atTop := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_massRate_eq_gap_div_spacing
  ] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformGap_div_spacing_tendsto_atTop
      s hs beta hbeta hbetaCutoff
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero

end

end MathlibAnalytic
end MGAP4D
