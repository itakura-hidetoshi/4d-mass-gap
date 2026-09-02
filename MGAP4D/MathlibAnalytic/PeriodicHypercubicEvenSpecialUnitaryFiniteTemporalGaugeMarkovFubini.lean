import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisRawPathGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finiteTemporalGaugeMarkovFubiniTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteTemporalGaugeMarkovFubiniCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteTemporalGaugeMarkovFubiniSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteTemporalGaugeMarkovFubiniMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteTemporalGaugeMarkovFubiniBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteTemporalGaugeMarkovFubiniSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance finiteTemporalGaugeMarkovFubiniBoundaryHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance finiteTemporalGaugeMarkovFubiniOpenHalfHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The rectangular completed Gram pairing is already the literal finite Wilson
path integral once the canonical `L²` representatives are exposed.  This is
the scalar entry point for the subsequent temporal-gauge/Fubini decomposition:
no abstract OS transfer, completion, or spectral hypothesis occurs here. -/
theorem periodicHypercubicEvenWilsonBoundaryGramPairing_eq_rawPath_integral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f u =
      ∫ p : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
        periodicHypercubicEvenWilsonBoundaryGramRawPathRectangularKernel
            H N hN beta hbeta p *
          (f p.1 * u p.2)
        ∂((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hK :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_eq_rawPath
      H N hN beta hbeta
  have hTensor :=
    realL2ExternalTensor_coeFn
      (μ := periodicHypercubicEvenBoundaryHaarMeasure H N)
      (ν := periodicHypercubicEvenOpenHalfHaarMeasure H N) f u
  filter_upwards [hK, hTensor] with p hpK hpTensor
  rw [hpK, hpTensor]
  simp [realL2ExternalTensorFunction, realL2Scalar_inner_eq_mul]

/-- The complete positive-half spatial-path Haar law splits exactly into its
first spatial slice and the remaining `H+1` spatial slices.  This is the finite
product-measure statement underlying the Markov recursion. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_headTail_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        0)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi
          (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
            periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
    (MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (0 : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1)))

/-- Finite Fubini decomposition of an integrable spatial-path functional into
the initial slice and the remaining path.  Keeping the canonical
`piFinSuccAbove` equivalence explicit avoids any ad-hoc tuple encoding and makes
this theorem directly reusable for induction over adjacent Wilson slabs. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_integral_headTail
    (H N : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N → ℝ)
    (hF : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) :
    ∫ path,
        F path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) =
      ∫ A₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∫ tail : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) →
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          F
            ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
              0).symm (A₀, tail))
          ∂(Measure.pi
            (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
              periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      0
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν := Measure.pi
    (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) => μ)
  have he :
      MeasurePreserving e
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
        (μ.prod ν) := by
    simpa [e, μ, ν] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_headTail_measurePreserving
        H N
  have hcomp : Integrable (F ∘ e.symm) (μ.prod ν) := by
    exact
      (he.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  calc
    (∫ path,
        F path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
        ∫ q, F (e.symm q) ∂(μ.prod ν) := by
      exact (he.symm.integral_comp' F).symm
    _ = ∫ A₀, ∫ tail, F (e.symm (A₀, tail)) ∂ν ∂μ := by
      simpa [Function.comp_def] using MeasureTheory.integral_prod _ hcomp
    _ = _ := by
      rfl

end

end MathlibAnalytic
end MGAP4D
