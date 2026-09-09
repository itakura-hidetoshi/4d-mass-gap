import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarAEDescent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Transport the shared-base Fubini descent across an exact measure-preserving
measurable equivalence.  This is the carrier-change lemma needed to apply the
product theorem to finite Haar coordinate reindexings without identifying
unrelated measurable presentations. -/
theorem aestronglyMeasurable_sharedBase_of_measurePreserving_equiv
    {Ω γ α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace α] [MeasurableSpace β]
    (ω : Measure Ω) (ρ : Measure γ) (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Ω ≃ᵐ ((γ × α) × β))
    (he : MeasurePreserving e ω ((ρ.prod μ).prod ν))
    (f : Ω → ℝ)
    (hleft : AEStronglyMeasurable[
      MeasurableSpace.comap (fun x : Ω => (e x).1)
        (inferInstance : MeasurableSpace (γ × α))] f ω)
    (hright : AEStronglyMeasurable[
      MeasurableSpace.comap (fun x : Ω => ((e x).1.1, (e x).2))
        (inferInstance : MeasurableSpace (γ × β))] f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap (fun x : Ω => (e x).1.1)
        (inferInstance : MeasurableSpace γ)] f ω := by
  let τ : Measure ((γ × α) × β) := (ρ.prod μ).prod ν
  let f' : ((γ × α) × β) → ℝ := fun y => f (e.symm y)
  have he_symm : MeasurePreserving e.symm τ ω :=
    MeasurePreserving.symm e he

  have hgLeft := hleft.stronglyMeasurable_mk
  obtain ⟨L, hL, hLfac⟩ := hgLeft.exists_eq_measurable_comp
  have hleft' :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace (γ × α))]
        f' τ := by
    refine ⟨fun y => L y.1, ?_, ?_⟩
    · exact hL.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · have h := he_symm.quasiMeasurePreserving.ae hleft.ae_eq_mk
      simpa [f', hLfac, Function.comp_def] using h

  have hgRight := hright.stronglyMeasurable_mk
  obtain ⟨R, hR, hRfac⟩ := hgRight.exists_eq_measurable_comp
  have hright' :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun y : (γ × α) × β => (y.1.1, y.2))
          (inferInstance : MeasurableSpace (γ × β))]
        f' τ := by
    refine ⟨fun y => R (y.1.1, y.2), ?_, ?_⟩
    · exact hR.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · have h := he_symm.quasiMeasurePreserving.ae hright.ae_eq_mk
      simpa [f', hRfac, Function.comp_def] using h

  have hbase' :=
    aestronglyMeasurable_sharedBase_of_left_right
      ρ μ ν f' hleft' hright'
  have hgBase := hbase'.stronglyMeasurable_mk
  obtain ⟨K, hK, hKfac⟩ := hgBase.exists_eq_measurable_comp
  refine ⟨fun x => K (e x).1.1, ?_, ?_⟩
  · exact hK.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · have h := he.quasiMeasurePreserving.ae hbase'.ae_eq_mk
    simpa [f', hKfac, Function.comp_def] using h

end

end MathlibAnalytic
end MGAP4D
