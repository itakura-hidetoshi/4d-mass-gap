import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Tilted

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

/-- Real `L²` for the product normalized Haar law on the finite Wilson
configuration space. -/
abbrev ContinuousCompactOrientedGaugeWilsonSystem.configurationHaarL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :=
  Lp ℝ 2 C.base.configurationHaarMeasure

/-- The inverse square root of the normalized Wilson Gibbs density, written in
an algebraically cancellation-friendly form.

If `Z` is the finite-volume partition function and `S` is the Gibbs exponent,
then this is `sqrt Z * exp (-S / 2)`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Weight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) : ℝ :=
  Real.sqrt C.base.partitionFunction *
    Real.exp (-C.base.gibbsExponent A / 2)

/-- The Wilson Haar-to-Gibbs `L²` weight is continuous. -/
theorem continuous_compact_oriented_haarToGibbsL2Weight_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Continuous C.haarToGibbsL2Weight := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Weight
  exact continuous_const.mul
    (Real.continuous_exp.comp
      ((continuous_compact_oriented_gibbsExponent C).neg.div_const 2))

/-- The Wilson Haar-to-Gibbs `L²` weight is strictly positive. -/
theorem continuous_compact_oriented_haarToGibbsL2Weight_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) :
    0 < C.haarToGibbsL2Weight A := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Weight
  exact mul_pos
    (Real.sqrt_pos.2
      (compact_oriented_partitionFunction_pos C.base
        (continuous_compact_oriented_boltzmannIntegrable C)))
    (Real.exp_pos _)

/-- Squaring the half-density exponential gives the inverse full Gibbs
exponential. -/
theorem continuous_compact_oriented_halfDensityExp_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) :
    Real.exp (-C.base.gibbsExponent A / 2) ^ 2 =
      Real.exp (-C.base.gibbsExponent A) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The unnormalized Gibbs exponential cancels the inverse-square-root weight
squared, leaving exactly the partition function. -/
theorem continuous_compact_oriented_exp_mul_haarToGibbsL2Weight_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) :
    Real.exp (C.base.gibbsExponent A) *
        C.haarToGibbsL2Weight A ^ 2 =
      C.base.partitionFunction := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Weight
  rw [mul_pow,
    Real.sq_sqrt
      (le_of_lt (compact_oriented_partitionFunction_pos C.base
        (continuous_compact_oriented_boltzmannIntegrable C))),
    continuous_compact_oriented_halfDensityExp_sq]
  calc
    Real.exp (C.base.gibbsExponent A) *
        (C.base.partitionFunction * Real.exp (-C.base.gibbsExponent A)) =
      C.base.partitionFunction *
        (Real.exp (C.base.gibbsExponent A) *
          Real.exp (-C.base.gibbsExponent A)) := by ring
    _ = C.base.partitionFunction := by
      rw [← Real.exp_add]
      simp

/-- The normalized Gibbs density times the weight squared is exactly one. -/
theorem continuous_compact_oriented_normalizedDensity_mul_haarToGibbsL2Weight_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) :
    (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) *
        C.haarToGibbsL2Weight A ^ 2 = 1 := by
  rw [div_mul_eq_mul_div,
    continuous_compact_oriented_exp_mul_haarToGibbsL2Weight_sq]
  exact div_self
    (ne_of_gt (compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)))

/-- The finite Wilson Gibbs law is absolutely continuous with respect to the
product Haar law. -/
theorem continuous_compact_oriented_gibbsMeasure_absolutelyContinuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.gibbsMeasure ≪ C.base.configurationHaarMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  exact tilted_absolutelyContinuous _ _

/-- Pointwise inverse-square-root density transport of a Haar `L²` vector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.haarToGibbsL2Function
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.configurationHaarL2)
    (A : C.base.Configuration) : ℝ :=
  C.haarToGibbsL2Weight A * f A

/-- The inverse-square-root density transport is ae-strongly measurable under
the Gibbs law. -/
theorem continuous_compact_oriented_haarToGibbsL2Function_aestronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.configurationHaarL2) :
    AEStronglyMeasurable (C.haarToGibbsL2Function f) C.gibbsMeasure := by
  apply AEStronglyMeasurable.mono_ac
    (continuous_compact_oriented_gibbsMeasure_absolutelyContinuous C)
  exact
    (continuous_compact_oriented_haarToGibbsL2Weight_continuous C).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)

/-- Every Haar `L²` vector transported by the inverse square root of the Gibbs
density belongs to Gibbs `L²`. -/
theorem continuous_compact_oriented_haarToGibbsL2Function_memLp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.configurationHaarL2) :
    MemLp (C.haarToGibbsL2Function f) 2 C.gibbsMeasure := by
  apply (memLp_two_iff_integrable_sq
    (continuous_compact_oriented_haarToGibbsL2Function_aestronglyMeasurable C f)).2
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [integrable_tilted_iff
    (continuous_compact_oriented_boltzmannIntegrable C)]
  have hf : Integrable (fun A => (f A) ^ 2) C.base.configurationHaarMeasure :=
    (Lp.memLp f).integrable_sq
  have hZ := hf.const_mul C.base.partitionFunction
  apply hZ.congr
  filter_upwards with A
  symm
  change
    Real.exp (C.base.gibbsExponent A) *
        ((C.haarToGibbsL2Weight A * f A) ^ 2) =
      C.base.partitionFunction * f A ^ 2
  rw [mul_pow]
  calc
    Real.exp (C.base.gibbsExponent A) *
        (C.haarToGibbsL2Weight A ^ 2 * f A ^ 2) =
      (Real.exp (C.base.gibbsExponent A) *
        C.haarToGibbsL2Weight A ^ 2) * f A ^ 2 := by ring
    _ = C.base.partitionFunction * f A ^ 2 := by
      rw [continuous_compact_oriented_exp_mul_haarToGibbsL2Weight_sq]

end

end MathlibAnalytic
end MGAP4D
