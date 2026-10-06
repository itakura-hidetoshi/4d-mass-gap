import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFiniteMassCriticalGap
import Mathlib.Tactic

/-!
# Finite posterior mass scaling must leave the decoupled beta regime

PR #5204 proves that every finite positive generator-scaling certificate forces

  alpha_bar(s,beta_n) -> 1.

At the decoupled point, however,

  alpha_bar(s,0) = 0,

and the coefficient is continuous at beta = 0.  Therefore beta_n cannot tend
to zero.  In fact a stronger statement holds: there is one positive beta floor
which beta_n eventually stays above.

This sharpens the continuum obstruction.  A finite continuum mass extracted
from the posterior full-sweep factor cannot be realized while remaining
asymptotically in the small-beta decoupled neighborhood.  The scale-dependent
coupling must eventually leave some fixed neighborhood of zero.

No existence theorem for a suitable critical coupling sequence, no
posterior-sweep / Euclidean-transfer identification, H1-D5 exact descent, or
complete Yang--Mills mass-gap theorem is asserted.
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

/-- A finite positive posterior generator-scaling certificate cannot have its
coupling sequence converge to the decoupled point beta = 0. -/
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
        s).tendsto.comp hBetaZero
    simpa [Function.comp_def] using h
  have hAlphaOne := A.coefficient_tendsto_one
  have hFalse : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hAlphaZero hAlphaOne
  norm_num at hFalse

/-- More strongly, every finite positive posterior generator-scaling
certificate eventually stays above one fixed positive coupling floor. -/
theorem exists_pos_eventually_le_beta
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    ∃ delta : ℝ,
      0 < delta ∧
      ∀ᶠ n : ℕ in atTop, delta ≤ beta n := by
  let alpha : ℝ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
      s
  have hAlphaAt : ContinuousAt alpha 0 := by
    simpa [alpha] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s
  rw [Metric.continuousAt_iff] at hAlphaAt
  obtain ⟨delta, hDelta, hControl⟩ :=
    hAlphaAt (1 / 2) (by norm_num)
  have hAlphaEventually :
      ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < alpha (beta n) := by
    have hTendsto :
        Tendsto (fun n => alpha (beta n)) atTop (nhds 1) := by
      simpa [alpha] using A.coefficient_tendsto_one
    exact (tendsto_order.1 hTendsto).1 (1 / 2) (by norm_num)
  refine ⟨delta, hDelta, ?_⟩
  filter_upwards [hAlphaEventually] with n hHalf
  by_contra hNot
  have hBetaLt : beta n < delta :=
    lt_of_not_ge hNot
  have hDist :
      dist (beta n) 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (A.beta_nonneg n)]
    exact hBetaLt
  have hImage := hControl hDist
  have hAlphaZero : alpha 0 = 0 := by
    simp [alpha]
  rw [hAlphaZero, Real.dist_eq, sub_zero] at hImage
  have hAlphaLt : alpha (beta n) < (1 / 2 : ℝ) :=
    (abs_lt.mp hImage).2
  exact (lt_asymm hHalf hAlphaLt).elim

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

end

end MathlibAnalytic
end MGAP4D
