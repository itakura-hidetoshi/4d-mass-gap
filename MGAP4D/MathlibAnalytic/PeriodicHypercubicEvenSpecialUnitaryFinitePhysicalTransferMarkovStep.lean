import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferRawIntegral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferMarkovStepTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferMarkovStepCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferMarkovStepSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferMarkovStepMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferMarkovStepBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferMarkovStepSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The first Markov tail itself splits canonically into its first spatial slice
`A₁` and the later `H` spatial slices.  This is the second finite product-measure
step needed to isolate the first two temporal boundaries `(A₀,A₁)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_tailHead_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        0)
      (Measure.pi
        (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi
          (fun _ : Fin H =>
            periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) := by
  simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using
    (MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (H + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (0 : Fin (H + 1)))

/-- Fubini decomposition of the first Markov tail into the adjacent slice `A₁`
and the later temporal path.  Together with the existing `A₀ × tail`
decomposition this exposes the first two spatial slices as the pair-Haar
variables used by the one-slab transfer matrix coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_integral_tailHead
    (H N : ℕ)
    (F :
      (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : Integrable F
      (Measure.pi
        (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) :
    (∫ tail,
        F tail
      ∂(Measure.pi
        (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
      ∫ A₁ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∫ laterTail : Fin H →
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          F
            ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
              0).symm (A₁, laterTail))
          ∂(Measure.pi
            (fun _ : Fin H =>
              periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      0
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν := Measure.pi (fun _ : Fin H => μ)
  have he :
      MeasurePreserving e
        (Measure.pi
          (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) => μ))
        (μ.prod ν) := by
    simpa [e, μ, ν] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_tailHead_measurePreserving
        H N
  have hcomp : Integrable (F ∘ e.symm) (μ.prod ν) := by
    exact
      (he.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  calc
    (∫ tail,
        F tail
      ∂(Measure.pi
        (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) => μ))) =
        ∫ q, F (e.symm q) ∂(μ.prod ν) := by
      exact (he.symm.integral_comp' F).symm
    _ = ∫ A₁, ∫ laterTail, F (e.symm (A₁, laterTail)) ∂ν ∂μ := by
      simpa [Function.comp_def] using MeasureTheory.integral_prod _ hcomp
    _ = _ := by
      rfl

/-- A factorized later-tail scalar can be carried through the first-slab raw
Haar integral and the latter can then be replaced exactly by the actual
physical one-slab transfer matrix coefficient.  This is the minimal cylinder
Markov step: the first slab is no longer represented by a literal kernel
integral, while the remaining finite temporal data is retained as an arbitrary
scalar tail functional. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_integral_laterTail
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (R : (Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    (∫ laterTail : Fin H →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta f) g *
          R laterTail
      ∂(Measure.pi
        (fun _ : Fin H =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
      ∫ laterTail : Fin H →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta p.1 p.2 *
              ((f : Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
                (g : Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.2) *
              R laterTail
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))
      ∂(Measure.pi
        (fun _ : Fin H =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  apply integral_congr_ae
  filter_upwards with laterTail
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral]
  rw [MeasureTheory.integral_mul_const]

end

end MathlibAnalytic
end MGAP4D
