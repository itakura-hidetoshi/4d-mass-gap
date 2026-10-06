import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFixedGapInfiniteMassRate
import Mathlib.Tactic

/-!
# Necessary coupling behavior for finite posterior generator scaling

PR #5202 packages a finite positive continuum mass through the exact
spacing-scaled posterior full-sweep gap

  (1 - alpha_bar(s,beta_n)) / a_n -> m > 0,

with positive lattice spacing a_n -> 0.  PR #5203 shows that a fixed beta in
the strict volume-uniform Dobrushin interval makes this rate diverge.

This file records the complementary necessary conditions for any scale-dependent
certificate that does have a finite positive mass:

  1. the unscaled Dobrushin gap must tend to zero;
  2. alpha_bar(s,beta_n) must tend to one;
  3. the canonical full-sweep factor rho(s,beta_n) must tend to one;
  4. beta_n cannot tend to the decoupled point beta = 0.

The last point follows from alpha_bar(s,0)=0 and continuity at zero.  Thus the
finite-mass scaling route cannot stay asymptotically in the small-beta
decoupled regime.  It must approach a regime where the certified Dobrushin gap
closes, or the physical duration assigned to one full sweep must be changed.

These are necessary conditions only.  No existence of such a beta_n sequence,
physical-time identification, H1-D5 exact descent, or complete Yang--Mills
mass-gap theorem is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

namespace
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

variable
    {s : ℝ}
    {hs : 8 < s}
    {latticeSpacing beta : ℕ → ℝ}

/-- Finite spacing-scaled gap together with spacing tending to zero forces the
unscaled posterior Dobrushin gap itself to vanish. -/
theorem gap_tendsto_zero
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    Tendsto
      (fun n =>
        1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s (beta n))
      atTop (nhds 0) := by
  have hProd :=
    A.gapRate_tendsto.mul A.latticeSpacing_tendsto_zero
  have hPointwise :
      (fun n =>
        ((1 -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
              s (beta n)) /
          latticeSpacing n) *
          latticeSpacing n) =
      (fun n =>
        1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s (beta n)) := by
    funext n
    have hSpacingNe : latticeSpacing n ≠ 0 :=
      ne_of_gt (A.latticeSpacing_pos n)
    field_simp [hSpacingNe]
  rw [hPointwise] at hProd
  simpa using hProd

/-- Equivalently, every finite-mass generator-scaling certificate drives the
volume-uniform posterior Dobrushin coefficient to the critical value one. -/
theorem coefficient_tendsto_one
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s (beta n))
      atTop (nhds 1) := by
  have h :=
    tendsto_const_nhds.sub A.gap_tendsto_zero
  simpa using h

/-- The corresponding full-sweep contraction factor must become critical as
well: rho(s,beta_n) tends to one. -/
theorem fullSweepRate_tendsto_one
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s (beta n))
      atTop (nhds 1) := by
  have hNeg :
      Tendsto
        (fun n =>
          -(
            1 -
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
                s (beta n)))
        atTop (nhds 0) := by
    simpa using A.gap_tendsto_zero.neg
  have hExp := hNeg.rexp
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  ] using hExp

/-- A finite positive generator-scaling certificate cannot have beta_n tending
to the decoupled point beta = 0. -/
theorem not_beta_tendsto_zero
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    ¬ Tendsto beta atTop (nhds 0) := by
  intro hBetaZero
  have hAlphaZero :
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s (beta n))
        atTop (nhds 0) := by
    have h :=
      (continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s).comp hBetaZero
    simpa using h
  have hAlphaOne := A.coefficient_tendsto_one
  have hFalse : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hAlphaZero hAlphaOne
  norm_num at hFalse

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

end

end MathlibAnalytic
end MGAP4D
