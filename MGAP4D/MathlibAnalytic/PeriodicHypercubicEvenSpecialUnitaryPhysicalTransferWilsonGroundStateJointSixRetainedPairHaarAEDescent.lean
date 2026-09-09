import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarAEMeasurability
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A product-measure a.e. gluing lemma with a common base.

On `((γ × α) × β, (ρ.prod μ).prod ν)`, suppose the same real function has
an a.e. strongly measurable version depending only on `(γ, α)` and another
one depending only on `(γ, β)`. Then it has an a.e. strongly measurable
version depending only on the common `γ` coordinate.

The proof is a direct Fubini argument. It does not use any exchange between
completion and intersection of sigma-algebras. In particular, it is suitable
for iterating finite independent Haar-coordinate elimination. -/
theorem aestronglyMeasurable_sharedBase_of_left_right
    {γ α β : Type*}
    [MeasurableSpace γ]
    [MeasurableSpace α]
    [MeasurableSpace β]
    (ρ : Measure γ)
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : (γ × α) × β → ℝ)
    (hleft :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace (γ × α))]
        f ((ρ.prod μ).prod ν))
    (hright :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun z : (γ × α) × β => (z.1.1, z.2))
          (inferInstance : MeasurableSpace (γ × β))]
        f ((ρ.prod μ).prod ν)) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        (fun z : (γ × α) × β => z.1.1)
        (inferInstance : MeasurableSpace γ)]
      f ((ρ.prod μ).prod ν) := by
  let leftMap : (γ × α) × β → γ × α := Prod.fst
  let rightMap : (γ × α) × β → γ × β := fun z => (z.1.1, z.2)
  let baseMap : (γ × α) × β → γ := fun z => z.1.1

  have hgLeft :
      StronglyMeasurable[
        MeasurableSpace.comap leftMap
          (inferInstance : MeasurableSpace (γ × α))]
        (hleft.mk f) := by
    simpa [leftMap] using hleft.stronglyMeasurable_mk
  obtain ⟨L, hL, hLfac⟩ := hgLeft.exists_eq_measurable_comp

  have hgRight :
      StronglyMeasurable[
        MeasurableSpace.comap rightMap
          (inferInstance : MeasurableSpace (γ × β))]
        (hright.mk f) := by
    simpa [rightMap] using hright.stronglyMeasurable_mk
  obtain ⟨R, hR, hRfac⟩ := hgRight.exists_eq_measurable_comp

  have hLR :
      (fun z : (γ × α) × β => L z.1) =ᵐ[(ρ.prod μ).prod ν]
        (fun z => R (z.1.1, z.2)) := by
    have hmk : hleft.mk f =ᵐ[(ρ.prod μ).prod ν] hright.mk f :=
      hleft.ae_eq_mk.symm.trans hright.ae_eq_mk
    rw [hLfac, hRfac] at hmk
    simpa [leftMap, rightMap, Function.comp_def] using hmk

  have hca :
      ∀ᵐ ca ∂ρ.prod μ, ∀ᵐ b ∂ν, L ca = R (ca.1, b) := by
    simpa using Measure.ae_ae_of_ae_prod hLR
  have hc :
      ∀ᵐ c ∂ρ, ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, L (c, a) = R (c, b) := by
    simpa using Measure.ae_ae_of_ae_prod hca

  let k : γ → ℝ := fun c => ∫ a, L (c, a) ∂μ
  have hk : StronglyMeasurable k := by
    simpa [k, Function.uncurry] using hL.integral_prod_right'

  have hcR : ∀ᵐ c ∂ρ, ∀ᵐ b ∂ν, k c = R (c, b) := by
    filter_upwards [hc] with c hc'
    have hswap :
        ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, L (c, a) = R (c, b) := by
      rw [← Measure.ae_ae_comm]
      · exact hc'
      · measurability
    filter_upwards [hswap] with b hb
    dsimp [k]
    calc
      (∫ a, L (c, a) ∂μ) = ∫ a, R (c, b) ∂μ := integral_congr_ae hb
      _ = R (c, b) := by simp

  have hcaR :
      ∀ᵐ ca ∂ρ.prod μ, ∀ᵐ b ∂ν, k ca.1 = R (ca.1, b) := by
    exact (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := μ)).ae hcR

  have hKR :
      (fun z : (γ × α) × β => k z.1.1) =ᵐ[(ρ.prod μ).prod ν]
        (fun z => R (z.1.1, z.2)) := by
    change ∀ᵐ z ∂(ρ.prod μ).prod ν, k z.1.1 = R (z.1.1, z.2)
    rw [Measure.ae_prod_iff_ae_ae]
    · exact hcaR
    · measurability

  have hfbase :
      f =ᵐ[(ρ.prod μ).prod ν] (fun z : (γ × α) × β => k z.1.1) := by
    have hrightRep :
        f =ᵐ[(ρ.prod μ).prod ν] (fun z => R (z.1.1, z.2)) := by
      have hrightAE := hright.ae_eq_mk
      rw [hRfac] at hrightAE
      simpa [rightMap, Function.comp_def] using hrightAE
    exact hrightRep.trans hKR.symm

  refine ⟨fun z => k (baseMap z), ?_, ?_⟩
  · exact hk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · simpa [baseMap] using hfbase

end

end MathlibAnalytic
end MGAP4D
