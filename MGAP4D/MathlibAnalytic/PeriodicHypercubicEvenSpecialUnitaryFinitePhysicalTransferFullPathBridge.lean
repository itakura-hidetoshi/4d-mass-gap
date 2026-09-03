import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferTwoEndedWilsonRecursion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFiniteTemporalGaugeMarkovFubini
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferFullPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferFullPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferFullPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferFullPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferFullPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferFullPathSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The complete positive-half spatial path is canonically the first adjacent
pair `(A₀,A₁)` together with the later path `A₂,…,A_{h+2}`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv
    (h N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N ≃ᵐ
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) ×
        (Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) :=
  let e₀ :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) + 1) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
      0
  let e₁ :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1)) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
      0
  e₀.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)) e₁).trans
      MeasurableEquiv.prodAssoc.symm)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv_symm_apply
    (h N : ℕ)
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
    (laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv
        h N).symm (p, laterTail) =
      Fin.cons p.1 (Fin.cons p.2 laterTail) := by
  let e₀ :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) + 1) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
      0
  let e₁ :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1)) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
      0
  change e₀.symm (p.1, e₁.symm (p.2, laterTail)) =
    Fin.cons p.1 (Fin.cons p.2 laterTail)
  have h₁ : e₁.symm (p.2, laterTail) = Fin.cons p.2 laterTail := by
    simp only [e₁, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero]
    rfl
  rw [h₁]
  simp only [e₀, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero]
  rfl

/-- The first-pair/later-tail coordinates preserve exactly pair Haar times the
remaining finite product Haar law. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTail_measurePreserving
    (h N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv h N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (h + 1) N)
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (h + 1) N).prod
        (Measure.pi (fun _ : Fin (h + 1) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N
  let ν := Measure.pi (fun _ : Fin (h + 1) => μ)
  have h₀ :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_headTail_measurePreserving
      (h + 1) N
  have h₁ :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_tailHead_measurePreserving
      (h + 1) N
  have hmid := (MeasurePreserving.id μ).prod h₁
  have hassoc :
      MeasurePreserving MeasurableEquiv.prodAssoc
        ((μ.prod μ).prod ν) (μ.prod (μ.prod ν)) := by
    refine ⟨MeasurableEquiv.prodAssoc.measurable, ?_⟩
    exact Measure.prodAssoc_prod
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount, μ, ν] using
    h₀.trans (hmid.trans hassoc.symm)

/-- Pointwise integrand of the complete temporal-gauge two-ended endpoint
amplitude.  Naming it keeps the Fubini interface independent of parser-level
complexity in the endpoint `L²` coercions. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand
    (h N : ℕ) (beta : ℝ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N) : ℝ :=
  ((f : Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) (path 0)) *
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
      (h + 1) N beta path *
    ((g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))
      (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1)))))

/-- The complete temporal-gauge two-ended endpoint path integral. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude
    (h N : ℕ) (beta : ℝ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) : ℝ :=
  ∫ path,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand h N beta f g path
  ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (h + 1) N)

/-- Once the endpoint path integrand is integrable, the complete temporal-gauge
path integral is exactly the literal two-ended Wilson amplitude in
`((A₀,A₁),laterTail)` coordinates. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_literal
    (h N : ℕ) (beta : ℝ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N)
    (hInt : Integrable
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand h N beta f g)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (h + 1) N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude h N beta f g =
      periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude h N beta f g := by
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv h N
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N
  let ν := Measure.pi (fun _ : Fin (h + 1) => μ)
  let F := periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand h N beta f g
  have he : MeasurePreserving e
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (h + 1) N)
      ((μ.prod μ).prod ν) := by
    simpa [e, μ, ν, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTail_measurePreserving h N
  have hcomp : Integrable (F ∘ e.symm) ((μ.prod μ).prod ν) := by
    exact (he.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hInt
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude h N beta f g =
        ∫ q, F (e.symm q) ∂((μ.prod μ).prod ν) := by
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude
      exact (he.symm.integral_comp' F).symm
    _ = ∫ laterTail, ∫ p, F (e.symm (p, laterTail)) ∂(μ.prod μ) ∂ν := by
      simpa [Function.comp_def] using MeasureTheory.integral_prod_symm _ hcomp
    _ = periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude h N beta f g := by
      unfold periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
      apply integral_congr_ae
      filter_upwards with laterTail
      apply integral_congr_ae
      filter_upwards with p
      rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfFirstPairLaterTailMeasurableEquiv_symm_apply]
      have hk :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_headTail
          (h + 1) N beta p.1 (Fin.cons p.2 laterTail)
      have hk' :
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              (h + 1) N beta (Fin.cons p.1 (Fin.cons p.2 laterTail)) =
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                (h + 1) N beta p.1 p.2 *
              ∏ x : Fin (h + 1),
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  (h + 1) N beta
                  ((Fin.cons p.2 laterTail : Fin ((h + 1) + 1) →
                    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
                    x.castSucc)
                  (laterTail x) := by
        simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero] using hk
      rw [hk']
      simp [F, periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand,
        μ, periodicHypercubicEvenPositiveHalfCylinderSlabCount]
      ring

end

end MathlibAnalytic
end MGAP4D