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
    [MeasurableSpace Ω]
    [MeasurableSpace γ]
    [MeasurableSpace α]
    [MeasurableSpace β]
    (ω : Measure Ω)
    (ρ : Measure γ)
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (e : Ω ≃ᵐ ((γ × α) × β))
    (he : MeasurePreserving e ω ((ρ.prod μ).prod ν))
    (f : Ω → ℝ)
    (hleft :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun x : Ω => (e x).1)
          (inferInstance : MeasurableSpace (γ × α))]
        f ω)
    (hright :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun x : Ω => ((e x).1.1, (e x).2))
          (inferInstance : MeasurableSpace (γ × β))]
        f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        (fun x : Ω => (e x).1.1)
        (inferInstance : MeasurableSpace γ)]
      f ω := by
  let τ : Measure ((γ × α) × β) := (ρ.prod μ).prod ν
  let f' : ((γ × α) × β) → ℝ := fun y => f (e.symm y)
  have he_symm : MeasurePreserving e.symm τ ω :=
    MeasurePreserving.symm e.symm he

  have hleft' :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace (γ × α))]
        f' τ := by
    rcases hleft with ⟨g, hg, hfg⟩
    refine ⟨fun y => g (e.symm y), ?_, ?_⟩
    · apply hg.comp_measurable
      apply measurable_iff_comap_le.mpr
      simp only [MeasurableSpace.comap_comap, Function.comp_def]
      simpa using
        (show
          MeasurableSpace.comap
              (fun y : (γ × α) × β => (e (e.symm y)).1)
              (inferInstance : MeasurableSpace (γ × α)) ≤
            MeasurableSpace.comap Prod.fst
              (inferInstance : MeasurableSpace (γ × α)) by
          simp)
    · have h := he_symm.quasiMeasurePreserving.ae hfg
      simpa [f', Function.comp_def] using h

  have hright' :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (fun y : (γ × α) × β => (y.1.1, y.2))
          (inferInstance : MeasurableSpace (γ × β))]
        f' τ := by
    rcases hright with ⟨g, hg, hfg⟩
    refine ⟨fun y => g (e.symm y), ?_, ?_⟩
    · apply hg.comp_measurable
      apply measurable_iff_comap_le.mpr
      simp only [MeasurableSpace.comap_comap, Function.comp_def]
      simpa using
        (show
          MeasurableSpace.comap
              (fun y : (γ × α) × β =>
                ((e (e.symm y)).1.1, (e (e.symm y)).2))
              (inferInstance : MeasurableSpace (γ × β)) ≤
            MeasurableSpace.comap
              (fun y : (γ × α) × β => (y.1.1, y.2))
              (inferInstance : MeasurableSpace (γ × β)) by
          simp)
    · have h := he_symm.quasiMeasurePreserving.ae hfg
      simpa [f', Function.comp_def] using h

  have hbase' :=
    aestronglyMeasurable_sharedBase_of_left_right
      ρ μ ν f' hleft' hright'
  rcases hbase' with ⟨g, hg, hfg⟩
  refine ⟨fun x => g (e x), ?_, ?_⟩
  · apply hg.comp_measurable
    apply measurable_iff_comap_le.mpr
    simp only [MeasurableSpace.comap_comap, Function.comp_def]
  · have h := he.quasiMeasurePreserving.ae hfg
    simpa [f', Function.comp_def] using h

end

end MathlibAnalytic
end MGAP4D
