import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic

/-!
# Conditional expectation over one factor of a product probability space

For a product probability measure `μ.prod ν`, the conditional distribution
of the second coordinate given the first is the constant kernel `ν`.
Consequently, conditional expectation onto the first-coordinate sigma-algebra
is literal integration over the second factor.

This is the generic Fubini input used downstream for the beta-zero
six-spatial pair-Haar commuting-square proof.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- Under a product probability law, the conditional distribution of the
second coordinate given the first is the constant second-factor law. -/
theorem condDistrib_snd_fst_prod_ae_eq_const
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    [StandardBorelSpace β]
    [Nonempty β]
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    condDistrib Prod.snd Prod.fst (μ.prod ν) =ᵐ[μ]
      Kernel.const α ν := by
  have hκ :
      (μ.prod ν).map (fun z : α × β => (z.1, z.2)) =
        (μ.prod ν).map Prod.fst ⊗ₘ Kernel.const α ν := by
    have hPair :
        (fun z : α × β => (z.1, z.2)) = id := by
      funext z
      rfl
    rw [hPair, Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul,
      Measure.compProd_const]
  have h :
      condDistrib Prod.snd Prod.fst (μ.prod ν) =ᵐ[(μ.prod ν).map Prod.fst]
        Kernel.const α ν := by
    exact
      condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
        (μ := μ.prod ν)
        (X := Prod.fst)
        (Y := Prod.snd)
        measurable_fst
        measurable_snd
        hκ
  simpa using h

/-- On a product probability space, conditional expectation onto the
first-coordinate sigma-algebra is fiber integration over the second factor. -/
theorem condExp_prod_fst_ae_eq_integral_snd
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    [StandardBorelSpace β]
    [Nonempty β]
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : α × β → ℝ)
    (hf : StronglyMeasurable f)
    (hf_int : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod ν]
      fun z => ∫ y, f (z.1, y) ∂ν := by
  have hcond :=
    condExp_prod_ae_eq_integral_condDistrib
      (μ := μ.prod ν)
      (X := Prod.fst)
      (Y := Prod.snd)
      measurable_fst
      measurable_snd.aemeasurable
      hf
      hf_int
  have hk :
      condDistrib Prod.snd Prod.fst (μ.prod ν) =ᵐ[μ]
        Kernel.const α ν :=
    condDistrib_snd_fst_prod_ae_eq_const μ ν
  have hkLift :
      ∀ᵐ z ∂μ.prod ν,
        condDistrib Prod.snd Prod.fst (μ.prod ν) z.1 =
          Kernel.const α ν z.1 := by
    exact
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hk
  refine hcond.trans ?_
  filter_upwards [hkLift] with z hz
  rw [hz]
  rfl

end

end MGAP4D.MathlibAnalytic
