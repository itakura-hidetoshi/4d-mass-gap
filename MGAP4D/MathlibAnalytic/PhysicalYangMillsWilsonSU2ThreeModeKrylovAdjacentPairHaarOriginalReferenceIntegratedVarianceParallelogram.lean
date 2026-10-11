import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiberParallelogram
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# P4-Q2-BK: rigorous outer integration of Haar-fiber parallelogram identities

BJ proves the evariance parallelogram for L² inputs on the LITERAL original
Wilson one-link Haar fiber, with the authentic mass weighting pointwise.

This file isolates the remaining integration theorem. The nonnegative
Lebesgue integral is additive when one summand is a.e.-measurable, but this
must NOT be assumed automatically for arbitrary context sections. Therefore
the integration bridge records the exact two relevant AEMeasurable premises
explicitly and uses pinned mathlib's lintegral_add_left' and
lintegral_const_mul' with no implicit independence or Tonelli equality.

The theorem works for the original weighted fiber construction of BH, and
is intended for specialization to the physical original Wilson outer Haar
product and its actual ground-state one-link mass after separate
measurability proofs. It is not itself a new Wilson-measure assumption,
a reverse Poincare theorem, or a continuum generator-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1200000

/-- Exactly the missing integral-additivity step. The original
one-link mass can serve as weight; finite mass is not required for this
extended-real equality. The two AEMeasurable premises are visible. -/
theorem p4Q2BK_weightedHaarFiberVariance_parallelogram
    {Outer SU : Type*}
    [MeasurableSpace Outer] [MeasurableSpace SU]
    (μOuter : Measure Outer) (μHaar : Measure SU)
    [IsFiniteMeasure μHaar]
    (weight : Outer → ENNReal) (F G : Outer → SU → ℝ)
    (hF : ∀ ctx, MemLp (F ctx) 2 μHaar)
    (hG : ∀ ctx, MemLp (G ctx) 2 μHaar)
    (hMeasPlus :
      AEMeasurable
        (fun ctx => weight ctx *
          evariance (fun u => F ctx u + G ctx u) μHaar)
        μOuter)
    (hMeasF :
      AEMeasurable
        (fun ctx => weight ctx * evariance (F ctx) μHaar)
        μOuter) :
    p4Q2BH_weightedHaarFiberVariance μOuter μHaar weight
        (fun ctx u => F ctx u + G ctx u) +
      p4Q2BH_weightedHaarFiberVariance μOuter μHaar weight
        (fun ctx u => F ctx u - G ctx u) =
      (2 : ENNReal) *
        (p4Q2BH_weightedHaarFiberVariance μOuter μHaar weight F +
          p4Q2BH_weightedHaarFiberVariance μOuter μHaar weight G) := by
  let plus : Outer → ENNReal := fun ctx =>
    weight ctx * evariance (fun u => F ctx u + G ctx u) μHaar
  let minus : Outer → ENNReal := fun ctx =>
    weight ctx * evariance (fun u => F ctx u - G ctx u) μHaar
  let xf : Outer → ENNReal := fun ctx =>
    weight ctx * evariance (F ctx) μHaar
  let yg : Outer → ENNReal := fun ctx =>
    weight ctx * evariance (G ctx) μHaar
  have hPlus : AEMeasurable plus μOuter := hMeasPlus
  have hX : AEMeasurable xf μOuter := hMeasF
  have hpoint (ctx : Outer) :
      plus ctx + minus ctx = (2 : ENNReal) * (xf ctx + yg ctx) := by
    dsimp [plus, minus, xf, yg]
    calc
      weight ctx * evariance (fun u => F ctx u + G ctx u) μHaar +
          weight ctx * evariance (fun u => F ctx u - G ctx u) μHaar =
        weight ctx *
          (evariance (fun u => F ctx u + G ctx u) μHaar +
            evariance (fun u => F ctx u - G ctx u) μHaar) := by
          rw [mul_add]
      _ = weight ctx *
            ((2 : ENNReal) *
              (evariance (F ctx) μHaar + evariance (G ctx) μHaar)) := by
          rw [p4Q2BJ_evariance_parallelogram
            μHaar (F ctx) (G ctx) (hF ctx) (hG ctx)]
      _ = (2 : ENNReal) *
            (weight ctx * evariance (F ctx) μHaar +
              weight ctx * evariance (G ctx) μHaar) := by
          rw [mul_add]
          ac_rfl
  change (∫⁻ ctx, plus ctx ∂μOuter) +
      (∫⁻ ctx, minus ctx ∂μOuter) =
    (2 : ENNReal) *
      ((∫⁻ ctx, xf ctx ∂μOuter) + (∫⁻ ctx, yg ctx ∂μOuter))
  calc
    (∫⁻ ctx, plus ctx ∂μOuter) +
        (∫⁻ ctx, minus ctx ∂μOuter) =
      ∫⁻ ctx, plus ctx + minus ctx ∂μOuter :=
      (lintegral_add_left' hPlus minus).symm
    _ = ∫⁻ ctx, (2 : ENNReal) * (xf ctx + yg ctx) ∂μOuter := by
      apply lintegral_congr
      intro ctx
      exact hpoint ctx
    _ = (2 : ENNReal) * (∫⁻ ctx, xf ctx + yg ctx ∂μOuter) :=
      lintegral_const_mul' (2 : ENNReal)
        (fun ctx => xf ctx + yg ctx) (by norm_num)
    _ = (2 : ENNReal) *
          ((∫⁻ ctx, xf ctx ∂μOuter) +
            (∫⁻ ctx, yg ctx ∂μOuter)) := by
      rw [lintegral_add_left' hX yg]

end

end MathlibAnalytic
end MGAP4D
