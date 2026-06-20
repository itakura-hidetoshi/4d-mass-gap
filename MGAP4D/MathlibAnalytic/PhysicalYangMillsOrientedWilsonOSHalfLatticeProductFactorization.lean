import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHalfLatticePeterWeyl
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Primitive density-factorization data for the finite-volume Wilson OS form.

The full Gibbs law is not assumed to split into independent positive and
negative halves.  Instead, after a measurable half-lattice splitting, its
pushforward is represented as a density with respect to the product of the two
half reference measures.  The interaction across the reflection plane remains
in this density and is subsequently identified with the Wilson crossing
kernel.

Thus the model-specific input is separated into four audit-visible claims:

* measurable splitting into the two half-configurations;
* a Radon--Nikodym density over the product half measure;
* factorization of the pulled-back observable through the split coordinates;
* identification of the density-weighted split observable with the two
  amplitudes and crossing kernel.

`integral_map`, the `withDensity` Bochner-integral identity, and Fubini then
generate the monolithic quadratic kernel formula required by
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
  gibbsDensity :
    ℕ → HalfConfiguration × HalfConfiguration → ℝ≥0∞
  gibbsDensity_aemeasurable :
    ∀ n, AEMeasurable (gibbsDensity n)
      (halfMeasure.prod halfMeasure)
  gibbsDensity_lt_top_ae :
    ∀ n, ∀ᵐ z ∂(halfMeasure.prod halfMeasure), gibbsDensity n z < ∞
  split_map_gibbsMeasure :
    ∀ n,
      Measure.map (split n)
          (E.system (L.subsequence n)).gibbsMeasure =
        (halfMeasure.prod halfMeasure).withDensity (gibbsDensity n)
  splitObservable :
    ℕ → D.positiveTimeSubalgebra →
      HalfConfiguration × HalfConfiguration → ℝ
  splitObservable_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable (splitObservable n F)
        ((halfMeasure.prod halfMeasure).withDensity (gibbsDensity n))
  quadraticObservable_pullback_eq_splitObservable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (U : (E.system (L.subsequence n)).base.Configuration),
      (((D.quadraticObservable F :
          physicalYangMillsGaugeInvariantObservableSubalgebra
            (G.toSymmetryLimit L)) :
        BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U)) =
        splitObservable n F (split n U)
  amplitude : ℕ → D.positiveTimeSubalgebra → HalfConfiguration → ℝ
  crossingKernel : ℕ → HalfConfiguration → HalfConfiguration → ℝ
  density_toReal_mul_splitObservable_eq_kernelQuadratic :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (z : HalfConfiguration × HalfConfiguration),
      (gibbsDensity n z).toReal * splitObservable n F z =
        amplitude n F z.1 * crossingKernel n z.1 z.2 *
          amplitude n F z.2
  kernelQuadratic_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun z : HalfConfiguration × HalfConfiguration =>
          amplitude n F z.1 * crossingKernel n z.1 z.2 *
            amplitude n F z.2)
        (halfMeasure.prod halfMeasure)

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorizationData.halfMeasurableSpace

/-- Density transport, pointwise Wilson factorization, and Fubini generate the
exact iterated half-lattice kernel formula. -/
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
    let muHalf : Measure (C.HalfConfiguration × C.HalfConfiguration) :=
      C.halfMeasure.prod C.halfMeasure
    let s : C.HalfConfiguration × C.HalfConfiguration → ℝ :=
      C.splitObservable n F
    let q : C.HalfConfiguration × C.HalfConfiguration → ℝ :=
      fun z =>
        C.amplitude n F z.1 * C.crossingKernel n z.1 z.2 *
          C.amplitude n F z.2
    have hsMap :
        AEStronglyMeasurable s
          (Measure.map (C.split n)
            (E.system (L.subsequence n)).gibbsMeasure) := by
      rw [C.split_map_gibbsMeasure n]
      exact (C.splitObservable_integrable n F).aestronglyMeasurable
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
        ∫ U, s (C.split n U)
          ∂(E.system (L.subsequence n)).gibbsMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun U =>
              C.quadraticObservable_pullback_eq_splitObservable n F U
      _ = ∫ z, s z
          ∂Measure.map (C.split n)
            (E.system (L.subsequence n)).gibbsMeasure := by
            symm
            exact MeasureTheory.integral_map
              (C.split_aemeasurable n) hsMap
      _ = ∫ z, s z ∂muHalf.withDensity (C.gibbsDensity n) := by
            rw [C.split_map_gibbsMeasure n]
      _ = ∫ z, (C.gibbsDensity n z).toReal • s z ∂muHalf := by
            exact
              MeasureTheory.integral_withDensity_eq_integral_toReal_smul₀
                (C.gibbsDensity_aemeasurable n)
                (C.gibbsDensity_lt_top_ae n)
                s
      _ = ∫ z, q z ∂muHalf := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              simpa [q, s, smul_eq_mul] using
                C.density_toReal_mul_splitObservable_eq_kernelQuadratic n F z
      _ = ∫ x, ∫ y,
          C.amplitude n F x * C.crossingKernel n x y *
            C.amplitude n F y
          ∂C.halfMeasure ∂C.halfMeasure := by
            letI : IsFiniteMeasure C.halfMeasure := C.halfMeasureFinite
            change
              (∫ z,
                C.amplitude n F z.1 * C.crossingKernel n z.1 z.2 *
                  C.amplitude n F z.2
                ∂(C.halfMeasure.prod C.halfMeasure)) = _
            rw [MeasureTheory.integral_prod]
            exact C.kernelQuadratic_integrable n F

end

end MathlibAnalytic
end MGAP4D
