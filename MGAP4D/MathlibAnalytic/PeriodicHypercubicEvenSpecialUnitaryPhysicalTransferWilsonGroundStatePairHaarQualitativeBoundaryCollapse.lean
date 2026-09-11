import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedLpMeasReverse
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- On a product probability space, a real function which is a.e. strongly
measurable with respect to both coordinate sigma-algebras is a.e. constant.
No integrability assumption is used.  The proof factors measurable
representatives through the two projections and applies Fubini directly. -/
theorem ae_eq_const_of_product_fst_snd_aestronglyMeasurable
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : α × β → ℝ)
    (hf_fst :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace α)]
        f (μ.prod ν))
    (hf_snd :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace β)]
        f (μ.prod ν)) :
    ∃ c : ℝ, f =ᵐ[μ.prod ν] fun _ => c := by
  have hgFst := hf_fst.stronglyMeasurable_mk
  obtain ⟨L, hL, hLfac⟩ := hgFst.exists_eq_measurable_comp
  have hgSnd := hf_snd.stronglyMeasurable_mk
  obtain ⟨R, hR, hRfac⟩ := hgSnd.exists_eq_measurable_comp
  have hLR :
      (fun z : α × β => L z.1) =ᵐ[μ.prod ν]
        (fun z => R z.2) := by
    have hmk : hf_fst.mk f =ᵐ[μ.prod ν] hf_snd.mk f :=
      hf_fst.ae_eq_mk.symm.trans hf_snd.ae_eq_mk
    rw [hLfac, hRfac] at hmk
    simpa [Function.comp_def] using hmk
  have hsections :
      ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, L a = R b := by
    simpa using Measure.ae_ae_of_ae_prod hLR
  obtain ⟨a0, ha0⟩ : ∃ a : α, ∀ᵐ b ∂ν, L a = R b :=
    Filter.Eventually.exists hsections
  have hb : ∀ᵐ b ∂ν, R b = L a0 :=
    ha0.mono fun b hb => hb.symm
  have hRconst :
      (fun z : α × β => R z.2) =ᵐ[μ.prod ν]
        (fun _ => L a0) := by
    exact
      (measurePreserving_snd (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hb
  have hfR : f =ᵐ[μ.prod ν] (fun z : α × β => R z.2) := by
    have h := hf_snd.ae_eq_mk
    rw [hRfac] at h
    simpa [Function.comp_def] using h
  exact ⟨L a0, hfR.trans hRconst⟩

local instance pairHaarQualitativeCollapseTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairHaarQualitativeCollapseCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairHaarQualitativeCollapseSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairHaarQualitativeCollapseMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairHaarQualitativeCollapseBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairHaarQualitativeCollapseSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Actual spatial pair-Haar specialization of the nonintegrable qualitative
coordinate-intersection theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_ae_eq_const_of_fst_snd_aestronglyMeasurable
    (H N : ℕ)
    (f :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf_fst :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
    (hf_snd :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
        f (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    ∃ c : ℝ,
      f =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        fun _ => c := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
      f (μ.prod μ) at hf_fst
  change
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))]
      f (μ.prod μ) at hf_snd
  change ∃ c : ℝ, f =ᵐ[μ.prod μ] fun _ => c
  exact ae_eq_const_of_product_fst_snd_aestronglyMeasurable
    μ μ f hf_fst hf_snd

end

end MathlibAnalytic
end MGAP4D
