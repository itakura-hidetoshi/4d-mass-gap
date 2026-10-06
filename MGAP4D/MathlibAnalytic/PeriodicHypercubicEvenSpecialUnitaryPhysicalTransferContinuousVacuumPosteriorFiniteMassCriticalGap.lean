import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFullSweepGeneratorScaling
import Mathlib.Tactic

/-!
# Finite posterior continuum mass forces critical closing of the sweep gap

PR #5202 packages the finite-mass scaling condition

  (1 - alpha_bar(s,beta_n)) / a_n -> m > 0

for positive lattice spacings a_n -> 0.  PR #5203 proves that a fixed positive
gap would instead make this rate diverge.

This file records the corresponding necessary critical behavior.  Under any
finite generator-scaling certificate,

  1 - alpha_bar(s,beta_n) -> 0,
  alpha_bar(s,beta_n) -> 1,
  rho(s,beta_n) -> 1,

where

  rho(s,beta) = exp(-(1 - alpha_bar(s,beta))).

Thus a finite positive continuum mass is compatible only with a closing
per-sweep Dobrushin gap.  The finite mass is retained in the first-order ratio
of that closing gap to lattice spacing, not in a fixed per-sweep contraction.

No existence theorem for such a coupling sequence beta_n is asserted here,
and no posterior-sweep / Euclidean-transfer identification is introduced.
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

/-- Finite spacing-scaled gap rate together with vanishing spacing forces the
unscaled posterior Dobrushin gap to close. -/
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
  have hEq :
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
    field_simp [ne_of_gt (A.latticeSpacing_pos n)]
  rw [hEq] at hProd
  simpa using hProd

/-- Equivalently, every finite-mass scaling certificate approaches the critical
Dobrushin value one. -/
theorem coefficient_tendsto_one
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s (beta n))
      atTop (nhds 1) := by
  have hOne :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h :=
    hOne.sub A.gap_tendsto_zero
  simpa using h

/-- The actual H-independent one-sweep contraction factor must tend to one in
every finite-mass scaling regime. -/
theorem fullSweepRate_tendsto_one
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s (beta n))
      atTop (nhds 1) := by
  have hArg :
      Tendsto
        (fun n =>
          -(1 -
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
              s (beta n)))
        atTop (nhds 0) := by
    simpa using A.gap_tendsto_zero.neg
  have hExp := hArg.rexp
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  ] using hExp

/-- The gap itself is asymptotically represented by its finite mass-rate times
the lattice spacing.  This exact identity makes explicit where the continuum
mass survives while the one-sweep gap vanishes. -/
theorem gap_eq_massRate_mul_spacing
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (n : ℕ) :
    1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s (beta n) =
      A.toPositiveDiscreteTransferRateLimit.massRate n *
        latticeSpacing n := by
  rw [A.massRate_eq_gap_div_spacing n]
  field_simp [ne_of_gt (A.latticeSpacing_pos n)]

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

end

end MathlibAnalytic
end MGAP4D
