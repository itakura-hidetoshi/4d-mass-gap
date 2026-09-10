import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureNormalizationIdentity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- A jointly a.e.-measurable family of nonnegative Doob weights whose fiber
masses are positive and finite almost everywhere admits an everywhere-defined
Markov-kernel representative.  The representative is required to agree, for
outer-almost every parameter, with the literal normalized `doobWeightedMeasure`
of the original fiber weight.

The construction first chooses Mathlib's measurable representative of the
joint weight, normalizes that representative as a kernel with density, and
then uses `Kernel.exists_ae_eq_isMarkovKernel` to patch only an outer null set.
The final a.e. equality is transported back to the original weight.  No RCD or
disintegration claim is made by this theorem. -/
theorem exists_doobWeightedMarkovKernel_ae_eq
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [SFinite ν]
    (w : α → β → ℝ≥0∞)
    (hw : AEMeasurable (Function.uncurry w) (μ.prod ν))
    (hμ : μ ≠ 0)
    (hMass : ∀ᵐ a ∂μ,
      0 < doobWeightMass ν (w a) ∧ doobWeightMass ν (w a) < ∞) :
    ∃ κ : Kernel α β,
      IsMarkovKernel κ ∧
        ∀ᵐ a ∂μ, κ a = doobWeightedMeasure ν (w a) := by
  let w' : α → β → ℝ≥0∞ :=
    Function.curry (hw.mk (Function.uncurry w))
  have hw' : Measurable (Function.uncurry w') := by
    simpa [w'] using hw.measurable_mk
  have hww' : ∀ᵐ a ∂μ, w a =ᵐ[ν] w' a := by
    simpa [w'] using Measure.ae_ae_eq_curry_of_prod hw.ae_eq_mk
  let Z' : α → ℝ≥0∞ := fun a => doobWeightMass ν (w' a)
  have hZ' : Measurable Z' := by
    simpa [Z', doobWeightMass] using
      (hw'.lintegral_kernel_prod_right (κ := Kernel.const α ν))
  let q : α → β → ℝ≥0∞ := fun a b => w' a b / Z' a
  have hq : Measurable (Function.uncurry q) := by
    change Measurable (fun p : α × β => w' p.1 p.2 / Z' p.1)
    exact hw'.div (hZ'.comp measurable_fst)
  let κ₀ : Kernel α β := Kernel.withDensity (Kernel.const α ν) q
  have hκ₀_apply (a : α) :
      κ₀ a = doobWeightedMeasure ν (w' a) := by
    change Kernel.withDensity (Kernel.const α ν) q a =
      doobWeightedMeasure ν (w' a)
    rw [Kernel.withDensity_apply _ hq]
    change ν.withDensity (fun b => w' a b / doobWeightMass ν (w' a)) =
      ν.withDensity (fun b => w' a b / doobWeightMass ν (w' a))
    rfl
  have hMassEq : ∀ᵐ a ∂μ,
      doobWeightMass ν (w a) = doobWeightMass ν (w' a) := by
    filter_upwards [hww'] with a ha
    simpa [doobWeightMass] using lintegral_congr_ae ha
  have hκ₀Prob : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ₀ a) := by
    filter_upwards [hMass, hMassEq] with a hmass hmassEq
    rw [hκ₀_apply a]
    refine ⟨doobWeightedMeasure_measure_univ ν (w' a)
      hw'.of_uncurry_left.aemeasurable ?_ ?_⟩
    · rw [← hmassEq]
      exact ne_of_gt hmass.1
    · rw [← hmassEq]
      exact ne_of_lt hmass.2
  obtain ⟨κ, hκ₀κ, hκMarkov⟩ :=
    Kernel.exists_ae_eq_isMarkovKernel (κ := κ₀) hκ₀Prob hμ
  refine ⟨κ, hκMarkov, ?_⟩
  filter_upwards [hκ₀κ, hww', hMassEq] with a hpatch hweight hmassEq
  have hmeasure :
      doobWeightedMeasure ν (w' a) = doobWeightedMeasure ν (w a) := by
    unfold doobWeightedMeasure
    apply withDensity_congr_ae
    filter_upwards [hweight] with b hb
    simp only [doobWeightedDensity]
    rw [← hb, ← hmassEq]
  exact hpatch.symm.trans ((hκ₀_apply a).trans hmeasure)

/-- Global exact normalization/disintegration identity for a jointly
AE-measurable Doob weight.  The outer measure is the reference measure `μ`,
while the exact fiber mass `doobWeightMass ν (w a)` is kept explicitly in the
integrand.  Equivalently, this is integration against the corresponding
weighted outer marginal, without yet identifying the kernel as an RCD. -/
theorem exists_doobWeightedMarkovKernel_lintegral_identity
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [SFinite ν]
    (w F : α → β → ℝ≥0∞)
    (hw : AEMeasurable (Function.uncurry w) (μ.prod ν))
    (hF : AEMeasurable (Function.uncurry F) (μ.prod ν))
    (hμ : μ ≠ 0)
    (hMass : ∀ᵐ a ∂μ,
      0 < doobWeightMass ν (w a) ∧ doobWeightMass ν (w a) < ∞) :
    ∃ κ : Kernel α β,
      IsMarkovKernel κ ∧
        (∀ᵐ a ∂μ, κ a = doobWeightedMeasure ν (w a)) ∧
        (∫⁻ z, w z.1 z.2 * F z.1 z.2 ∂(μ.prod ν)) =
          ∫⁻ a, doobWeightMass ν (w a) * (∫⁻ b, F a b ∂κ a) ∂μ := by
  obtain ⟨κ, hκMarkov, hκ⟩ :=
    exists_doobWeightedMarkovKernel_ae_eq μ ν w hw hμ hMass
  have hwFiber : ∀ᵐ a ∂μ, AEMeasurable (w a) ν := by
    exact hw.aestronglyMeasurable.prodMk_left.mono fun _ h => h.aemeasurable
  have hFFiber : ∀ᵐ a ∂μ, AEMeasurable (F a) ν := by
    exact hF.aestronglyMeasurable.prodMk_left.mono fun _ h => h.aemeasurable
  refine ⟨κ, hκMarkov, hκ, ?_⟩
  change
    (∫⁻ z, Function.uncurry w z * Function.uncurry F z ∂(μ.prod ν)) =
      ∫⁻ a, doobWeightMass ν (w a) * (∫⁻ b, F a b ∂κ a) ∂μ
  rw [lintegral_prod _ (hw.mul hF)]
  apply lintegral_congr_ae
  filter_upwards [hκ, hMass, hwFiber, hFFiber] with a hκa hmassa hwa hFa
  rw [hκa]
  exact (doobWeightMass_mul_lintegral_doobWeightedMeasure
    ν (w a) (F a) hwa hFa (ne_of_gt hmassa.1) (ne_of_lt hmassa.2)).symm

end

end MathlibAnalytic
end MGAP4D
