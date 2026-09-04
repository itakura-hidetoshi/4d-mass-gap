import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepPathKernelIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfOuterInnerDeepFubiniIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfOuterInnerDeepFubiniCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfOuterInnerDeepFubiniSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfOuterInnerDeepFubiniMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfOuterInnerDeepFubiniBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfOuterInnerDeepFubiniSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

/-- The literal temporal-gauge path kernel is continuous on the finite product
of spatial-slice configuration spaces.  This is only finite-product topology:
each slab factor is continuous and the full path kernel is their finite
product. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_continuous
    (M N : ℕ)
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta) := by
  classical
  let I := Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (M + 2))
  let Path :=
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N
  let factor : I → Path → ℝ := fun i path =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel (M + 2) N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)
  have hFactor : ∀ i : I, Continuous (factor i) := by
    intro i
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        (M + 2) N beta).comp₂
        (continuous_apply i.castSucc)
        (continuous_apply i.succ)
  have hProd : ∀ s : Finset I,
      Continuous (fun path : Path => s.prod (fun i => factor i path)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (continuous_const : Continuous (fun _ : Path => (1 : ℝ)))
    | @insert a s ha ih =>
        simpa [Finset.prod_insert, ha] using (hFactor a).mul ih
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
  change Continuous (fun path : Path => (Finset.univ : Finset I).prod (fun i => factor i path))
  exact hProd Finset.univ

/-- At nonnegative coupling the complete path kernel is Bochner-integrable
against product spatial-path Haar.  Continuity supplies measurability and the
already-proved pointwise Wilson bound supplies the uniform integrable majorant
`1` on the probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_integrable
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N) := by
  letI : IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N) := by
    infer_instance
  exact Integrable.of_bound
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_continuous
      M N beta).measurable.aestronglyMeasurable
    1
    (Filter.Eventually.of_forall fun path => by
      simpa [Real.norm_eq_abs] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
          (M + 2) N hN beta hbeta path)

/-- The Markov integrand on `outerPair × (innerPair × deep)` is integrable.
This is transported from the literal path-kernel integrability through the
same measure-preserving measurable equivalence used for the exact integral
change of variables. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_integrable
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
        M N beta)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv M N
  let F :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand M N beta
  have hPath :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_integrable
      M N hN beta hbeta
  have hPull :
      Integrable (F ∘ e)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N) := by
    exact hPath.congr (Filter.Eventually.of_forall fun path => by
      simpa [F, e, Function.comp_apply] using
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_comp
          M N hN beta hbeta path).symm)
  have hTransport :
      MeasurePreserving e
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
    simpa [e] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv_measurePreserving
        M N)
  have hF :
      Integrable F
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) :=
    (hTransport.integrable_comp_emb e.measurableEmbedding).mp hPull
  simpa [F] using hF

/-- Fubini exposes the three independent Haar integrations without adding a
pointwise fiber-integrability assumption.  The second application uses
`Integrable.prod_right_ae`, exactly matching Mathlib's a.e. section theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_integral_eq_iterated
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫ q,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
        M N beta q
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N)) =
      ∫ outer, ∫ inner, ∫ deep,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
          M N beta (outer, (inner, deep))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  let μPair := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N
  let μDeep :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N
  let F :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand M N beta
  have hF : Integrable F (μPair.prod (μPair.prod μDeep)) := by
    simpa [F, μPair, μDeep,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_integrable
        M N hN beta hbeta)
  have hFirst :
      (∫ q, F q ∂μPair.prod (μPair.prod μDeep)) =
        ∫ outer, ∫ rest, F (outer, rest) ∂μPair.prod μDeep ∂μPair := by
    exact MeasureTheory.integral_prod _ hF
  have hSecond :
      (∫ outer, ∫ rest, F (outer, rest) ∂μPair.prod μDeep ∂μPair) =
        ∫ outer, ∫ inner, ∫ deep, F (outer, (inner, deep)) ∂μDeep ∂μPair ∂μPair := by
    apply integral_congr_ae
    filter_upwards [hF.prod_right_ae] with outer hFiber
    exact MeasureTheory.integral_prod _ hFiber
  simpa [F, μPair, μDeep,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure] using
    hFirst.trans hSecond

/-- Final nondegenerate finite-volume Fubini form of the complete temporal-gauge
path-kernel integral.  The outer and inward ordered endpoint pairs now appear
as independent pair-Haar variables, ready for identification with the ambient
pair-Haar Hilbert--Schmidt transfer operator; only the deeper Wilson product
remains under the innermost Haar integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_outer_inner_deep
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
      ∫ outer, ∫ inner, ∫ deep,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
          M N beta (outer, (inner, deep))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  calc
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
        ∫ q,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
            M N beta q
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_outerInnerDeep
        M N hN beta hbeta
    _ = ∫ outer, ∫ inner, ∫ deep,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
          M N beta (outer, (inner, deep))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_integral_eq_iterated
        M N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
