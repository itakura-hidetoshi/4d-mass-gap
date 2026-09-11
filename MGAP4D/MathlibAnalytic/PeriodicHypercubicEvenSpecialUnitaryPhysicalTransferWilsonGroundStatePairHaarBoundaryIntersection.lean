import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- On a product probability space, an integrable real function which is almost-everywhere
strongly measurable with respect to both coordinate sigma-algebras agrees almost everywhere
with its mean.  This is the probabilistic intersection step used below; it does not identify
any physical fixed space by itself. -/
theorem ae_eq_integral_of_product_fst_snd_aestronglyMeasurable
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : α × β → ℝ)
    (hf_int : Integrable f (μ.prod ν))
    (hf_fst :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace α)]
        f (μ.prod ν))
    (hf_snd :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β)]
        f (μ.prod ν)) :
    f =ᵐ[μ.prod ν] fun _ => ∫ z, f z ∂(μ.prod ν) := by
  let g : α × β → ℝ := hf_fst.mk f
  have hfg : f =ᵐ[μ.prod ν] g := by
    exact hf_fst.ae_eq_mk
  have hg_fst :
      StronglyMeasurable[
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace α)] g := by
    exact hf_fst.stronglyMeasurable_mk
  have hg_snd :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β)]
        g (μ.prod ν) :=
    hf_snd.congr hfg
  have hg_int : Integrable g (μ.prod ν) := hf_int.congr hfg
  have hle_fst :
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace α) ≤
        (inferInstance : MeasurableSpace (α × β)) := by
    exact measurable_fst.comap_le
  have hle_snd :
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β) ≤
        (inferInstance : MeasurableSpace (α × β)) := by
    exact measurable_snd.comap_le
  have hindep :
      Indep
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace α))
        (MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β))
        (μ.prod ν) := by
    change IndepFun Prod.fst Prod.snd (μ.prod ν)
    simpa using
      (indepFun_prod
        (μ := μ) (ν := ν) (X := id) (Y := id)
        measurable_id measurable_id)
  have hself :=
    condExp_of_aestronglyMeasurable'
      (μ := μ.prod ν) hle_snd hg_snd hg_int
  have hmean :=
    condExp_indep_eq
      (μ := μ.prod ν) hle_fst hle_snd hg_fst hindep
  have hg_mean :
      g =ᵐ[μ.prod ν] fun _ => ∫ z, g z ∂(μ.prod ν) :=
    hself.symm.trans hmean
  calc
    f =ᵐ[μ.prod ν] g := hfg
    _ =ᵐ[μ.prod ν] (fun _ => ∫ z, g z ∂(μ.prod ν)) := hg_mean
    _ =ᵐ[μ.prod ν] (fun _ => ∫ z, f z ∂(μ.prod ν)) := by
      rw [integral_congr_ae hfg]

/-- The product-space intersection statement directly on the real L² carrier: membership in both
coordinate `lpMeas` submodules forces the represented function to be mean-valued almost
everywhere. -/
theorem ae_eq_integral_of_product_fst_snd_mem_lpMeas
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (f : Lp ℝ 2 (μ.prod ν))
    (hf_fst :
      f ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace α))
        2 (μ.prod ν))
    (hf_snd :
      f ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β))
        2 (μ.prod ν)) :
    (f : α × β → ℝ) =ᵐ[μ.prod ν]
      fun _ => ∫ z, f z ∂(μ.prod ν) := by
  have hf_int : Integrable (f : α × β → ℝ) (μ.prod ν) :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent one_le_two)
  exact ae_eq_integral_of_product_fst_snd_aestronglyMeasurable
    μ ν f hf_int
      (mem_lpMeas_iff_aestronglyMeasurable.mp hf_fst)
      (mem_lpMeas_iff_aestronglyMeasurable.mp hf_snd)

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For the actual spatial pair-Haar reference law, simultaneous almost-everywhere boundary
measurability forces an integrable real representative to agree almost everywhere with its mean.
This is only a reference-measure statement; transporting fixed-space information into its
hypotheses is a separate step. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_ae_eq_integral_of_fst_snd_aestronglyMeasurable
    (H N : ℕ)
    (f :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf_int :
      Integrable f
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
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
    f =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun _ =>
        ∫ z, f z
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change Integrable f (μ.prod μ) at hf_int
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
  change
    f =ᵐ[μ.prod μ] fun _ => ∫ z, f z ∂(μ.prod μ)
  exact ae_eq_integral_of_product_fst_snd_aestronglyMeasurable
    μ μ f hf_int hf_fst hf_snd

/-- The preceding product-space result specialized to the actual spatial pair-Haar real L²
carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_ae_eq_integral_of_mem_fst_snd_lpMeas
    (H N : ℕ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
    (hf_fst :
      f ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
    (hf_snd :
      f ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    (f :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun _ =>
        ∫ z, f z
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change
    f ∈ lpMeas ℝ ℝ
      (MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
      2 (μ.prod μ) at hf_fst
  change
    f ∈ lpMeas ℝ ℝ
      (MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
      2 (μ.prod μ) at hf_snd
  change
    (f :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) =ᵐ[μ.prod μ]
      fun _ => ∫ z, f z ∂(μ.prod μ)
  exact ae_eq_integral_of_product_fst_snd_mem_lpMeas μ μ f hf_fst hf_snd

end

end MathlibAnalytic
end MGAP4D
