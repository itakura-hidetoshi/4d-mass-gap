import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHalfLatticePeterWeyl
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Primitive product-factorization data for the finite-volume Wilson OS form.

This record separates the difficult geometric input into three audit-visible
claims:

* a measurable splitting of every full lattice configuration into positive and
  reflected half-configurations;
* transport of the finite-volume Gibbs measure to the product half measure;
* pointwise factorization of the pulled-back OS quadratic observable into two
  amplitudes and a crossing kernel.

Fubini and `MeasureTheory.integral_map` then generate the monolithic quadratic
kernel-integral identity required by
`PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition`. -/
structure PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorizationData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  HalfConfiguration : Type
  [halfMeasurableSpace : MeasurableSpace HalfConfiguration]
  halfMeasure : Measure HalfConfiguration
  halfMeasureFinite : IsFiniteMeasure halfMeasure
  split :
    ∀ n,
      (E.system (L.subsequence n)).base.Configuration →
        HalfConfiguration × HalfConfiguration
  split_aemeasurable :
    ∀ n, AEMeasurable (split n)
      (E.system (L.subsequence n)).gibbsMeasure
  split_map_gibbsMeasure :
    ∀ n,
      Measure.map (split n)
          (E.system (L.subsequence n)).gibbsMeasure =
        halfMeasure.prod halfMeasure
  amplitude : ℕ → D.positiveTimeSubalgebra → HalfConfiguration → ℝ
  crossingKernel : ℕ → HalfConfiguration → HalfConfiguration → ℝ
  kernelQuadratic_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun z : HalfConfiguration × HalfConfiguration =>
          amplitude n F z.1 * crossingKernel n z.1 z.2 *
            amplitude n F z.2)
        (halfMeasure.prod halfMeasure)
  quadraticObservable_pullback_eq_splitKernel :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (U : (E.system (L.subsequence n)).base.Configuration),
      (((D.quadraticObservable F :
          physicalYangMillsGaugeInvariantObservableSubalgebra
            (G.toSymmetryLimit L)) :
        BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U)) =
        amplitude n F (split n U).1 *
          crossingKernel n (split n U).1 (split n U).2 *
            amplitude n F (split n U).2

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorizationData.halfMeasurableSpace

/-- Product-measure transport and pointwise factorization generate the exact
iterated half-lattice kernel formula by change of variables and Fubini. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorizationData.toHalfLatticeDecomposition
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorizationData
      G L D) :
    PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D where
  HalfConfiguration := C.HalfConfiguration
  halfMeasure := C.halfMeasure
  amplitude := C.amplitude
  crossingKernel := C.crossingKernel
  pullbackForm_eq_kernelQuadratic := by
    intro n F
    let q : C.HalfConfiguration × C.HalfConfiguration → ℝ :=
      fun z =>
        C.amplitude n F z.1 * C.crossingKernel n z.1 z.2 *
          C.amplitude n F z.2
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.orientedWilsonPullbackForm
    calc
      (∫ U,
          (((D.quadraticObservable F :
              physicalYangMillsGaugeInvariantObservableSubalgebra
                (G.toSymmetryLimit L)) :
            BoundedContinuousFunction
              (G.toSymmetryLimit L).Configuration ℝ)
              (E.interpolate (L.subsequence n) U))
          ∂(E.system (L.subsequence n)).gibbsMeasure) =
        ∫ U, q (C.split n U)
          ∂(E.system (L.subsequence n)).gibbsMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun U =>
              C.quadraticObservable_pullback_eq_splitKernel n F U
      _ = ∫ z, q z
          ∂Measure.map (C.split n)
            (E.system (L.subsequence n)).gibbsMeasure := by
            symm
            exact MeasureTheory.integral_map
              (C.split_aemeasurable n)
              (C.kernelQuadratic_integrable n F).aestronglyMeasurable
      _ = ∫ z, q z ∂(C.halfMeasure.prod C.halfMeasure) := by
            rw [C.split_map_gibbsMeasure n]
      _ = ∫ x, ∫ y,
          C.amplitude n F x * C.crossingKernel n x y *
            C.amplitude n F y
          ∂C.halfMeasure ∂C.halfMeasure := by
            letI : IsFiniteMeasure C.halfMeasure := C.halfMeasureFinite
            rw [MeasureTheory.integral_prod]
            exact C.kernelQuadratic_integrable n F

end

end MathlibAnalytic
end MGAP4D
