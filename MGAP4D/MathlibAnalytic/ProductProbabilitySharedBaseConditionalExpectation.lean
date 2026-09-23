import MGAP4D.MathlibAnalytic.ProductProbabilityConditionalExpectationFiberFormula
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

/-!
# Shared-base conditional expectation on a three-factor product

On the product probability space

  ((γ × α) × β, (ρ.prod μ).prod ν),

a function depending only on the right retained coordinates `(γ, β)`,
when conditionally averaged onto the left retained coordinates `(γ, α)`,
collapses to a function of the common base `γ` alone.

This is exactly the range-invariance statement needed for commuting
product-Haar conditional-expectation projections.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

/-- If `g` depends on `(γ,β)`, then conditional expectation of its pullback
onto `(γ,α)` is literal integration over `β`, hence depends only on `γ`. -/
theorem condExp_triple_left_of_right_factor_ae_eq_common_integral
    {γ α β : Type*}
    [MeasurableSpace γ]
    [MeasurableSpace α]
    [MeasurableSpace β]
    [StandardBorelSpace β]
    [Nonempty β]
    (ρ : Measure γ)
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (g : γ × β → ℝ)
    (hg : StronglyMeasurable g)
    (hg_int :
      Integrable
        (fun z : (γ × α) × β => g (z.1.1, z.2))
        ((ρ.prod μ).prod ν)) :
    ((ρ.prod μ).prod ν)[
        (fun z : (γ × α) × β => g (z.1.1, z.2)) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[(ρ.prod μ).prod ν]
      fun z => ∫ b, g (z.1.1, b) ∂ν := by
  let F : (γ × α) × β → ℝ := fun z => g (z.1.1, z.2)
  have hF : StronglyMeasurable F := by
    exact hg.comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h :=
    condExp_prod_fst_ae_eq_integral_snd
      (ρ.prod μ) ν F hF hg_int
  simpa [F] using h

/-- A strongly right-retained measurable integrable function has a left
conditional expectation which is a.e. strongly measurable with respect to the
common base alone. -/
theorem condExp_triple_left_aestronglyMeasurable_common_of_right
    {γ α β : Type*}
    [MeasurableSpace γ]
    [MeasurableSpace α]
    [MeasurableSpace β]
    [StandardBorelSpace β]
    [Nonempty β]
    (ρ : Measure γ)
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : (γ × α) × β → ℝ)
    (hfRight :
      StronglyMeasurable[
        MeasurableSpace.comap
          (fun z : (γ × α) × β => (z.1.1, z.2))
          (inferInstance : MeasurableSpace (γ × β))]
        f)
    (hfInt : Integrable f ((ρ.prod μ).prod ν)) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        (fun z : (γ × α) × β => z.1.1)
        (inferInstance : MeasurableSpace γ)]
      (((ρ.prod μ).prod ν)[
        f | MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace (γ × α))])
      ((ρ.prod μ).prod ν) := by
  let rightMap : (γ × α) × β → γ × β :=
    fun z => (z.1.1, z.2)
  have hfRight' :
      StronglyMeasurable[
        MeasurableSpace.comap rightMap
          (inferInstance : MeasurableSpace (γ × β))]
        f := by
    simpa [rightMap] using hfRight
  obtain ⟨g, hg, hfac⟩ := hfRight'.exists_eq_measurable_comp
  have hfInt' :
      Integrable
        (fun z : (γ × α) × β => g (z.1.1, z.2))
        ((ρ.prod μ).prod ν) := by
    rw [hfac] at hfInt
    simpa [rightMap, Function.comp_def] using hfInt
  have hcond :=
    condExp_triple_left_of_right_factor_ae_eq_common_integral
      ρ μ ν g hg hfInt'
  let k : γ → ℝ := fun c => ∫ b, g (c, b) ∂ν
  have hk : StronglyMeasurable k := by
    simpa [k, Function.uncurry] using hg.integral_prod_right'
  have hkPull :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun z : (γ × α) × β => z.1.1)
          (inferInstance : MeasurableSpace γ)]
        (fun z : (γ × α) × β => k z.1.1)
        ((ρ.prod μ).prod ν) := by
    exact
      (hk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable
  have hfac' :
      f = (fun z : (γ × α) × β => g (z.1.1, z.2)) := by
    simpa [rightMap, Function.comp_def] using hfac
  have hcond' :
      ((ρ.prod μ).prod ν)[
          f | MeasurableSpace.comap Prod.fst
            (inferInstance : MeasurableSpace (γ × α))] =ᵐ[(ρ.prod μ).prod ν]
        fun z => k z.1.1 := by
    rw [hfac']
    simpa [k] using hcond
  exact hkPull.congr hcond'.symm

end

end MGAP4D.MathlibAnalytic
