import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureNorm
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureMeasurability

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Even-periodic local Wilson data with only an amplitude bound.

The exact Wilson RKHS feature of every crossing plaquette has unit norm, and so
does their finite completed-tensor product.  Therefore the norm of the weighted
global feature is exactly the absolute value of the scalar amplitude. -/
structure PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (N : ℕ)
    (beta : ℕ → ℝ)
    (halfExtent : ℕ → ℕ) where
  hN : 0 < N
  hbeta : ∀ n, 0 ≤ beta n
  positiveHalfHolonomy :
    ∀ n, PeriodicHypercubicEvenCrossingPlaquetteLabel (halfExtent n) →
      H.HalfConfiguration → Matrix.specialUnitaryGroup (Fin N) ℂ
  crossingKernel_eq_localWilsonProduct :
    ∀ (n : ℕ) (x y : H.HalfConfiguration),
      H.crossingKernel n x y =
        ((periodicHypercubicEvenCrossingPlaquetteList (halfExtent n)).map fun p =>
          localCrossingWilsonKernel N (beta n)
            (positiveHalfHolonomy n p) x y).prod
  halfMeasureFinite : IsFiniteMeasure H.halfMeasure
  weightedGlobalFeature_aestronglyMeasurable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      AEStronglyMeasurable
        (fun x => H.amplitude n F x •
          (RealHilbertKernelFeature.listProd
            (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
            (fun p =>
              localCrossingWilsonKernel N (beta n)
                (positiveHalfHolonomy n p))
            (fun p =>
              localCrossingWilsonKernelConcreteFeature
                N hN (beta n) (hbeta n) (positiveHalfHolonomy n p))).feature x)
        H.halfMeasure
  amplitudeBound : ℕ → D.positiveTimeSubalgebra → ℝ
  amplitude_abs_le :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) (x : H.HalfConfiguration),
      |H.amplitude n F x| ≤ amplitudeBound n F

/-- The exact unit-norm feature theorem turns an amplitude bound into the
weighted-global-feature norm bound required by the finite-measure constructor. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData.toBoundedLocalKernelData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData
      H N beta halfExtent) :
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelData
      H N beta halfExtent where
  hN := C.hN
  hbeta := C.hbeta
  positiveHalfHolonomy := C.positiveHalfHolonomy
  crossingKernel_eq_localWilsonProduct :=
    C.crossingKernel_eq_localWilsonProduct
  halfMeasureFinite := C.halfMeasureFinite
  weightedGlobalFeature_aestronglyMeasurable :=
    C.weightedGlobalFeature_aestronglyMeasurable
  weightedGlobalFeatureBound := C.amplitudeBound
  weightedGlobalFeature_norm_le := by
    intro n F x
    calc
      ‖H.amplitude n F x •
          (RealHilbertKernelFeature.listProd
            (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
            (fun p =>
              localCrossingWilsonKernel N (beta n)
                (C.positiveHalfHolonomy n p))
            (fun p =>
              localCrossingWilsonKernelConcreteFeature
                N C.hN (beta n) (C.hbeta n)
                  (C.positiveHalfHolonomy n p))).feature x‖ =
          |H.amplitude n F x| := by
        rw [norm_smul]
        rw [localCrossingWilsonKernelConcreteFeature_listProd_norm_eq_one
          N C.hN (beta n) (C.hbeta n)
          (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
          (C.positiveHalfHolonomy n) x]
        simp
      _ ≤ C.amplitudeBound n F := C.amplitude_abs_le n F x

/-- An amplitude bound and finite half measure imply reflection positivity of
every approximating physical lattice state. -/
theorem physical_yang_mills_oriented_evenPeriodicAmplitudeBoundedLocalKernel_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData
      H N beta halfExtent)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_evenPeriodicBoundedLocalKernel_approximating_reflectionPositive
    G L D H C.toBoundedLocalKernelData n

/-- An amplitude bound and finite half measure imply continuum
Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_evenPeriodicAmplitudeBoundedLocalKernel_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData
      H N beta halfExtent) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_evenPeriodicBoundedLocalKernel_continuum_reflectionPositive
    G L D H C.toBoundedLocalKernelData

/-- A locally factored measurability interface for the exact Wilson constructor.

Instead of assuming measurability of the amplitude-weighted global feature as a
single compound function, this package asks separately for measurability of the
scalar amplitude and of each one-plaquette Wilson RKHS feature.  The finite
completed-tensor-product global feature is then measurable automatically, and
Mathlib combines it with the amplitude using `AEStronglyMeasurable.smul`. -/
structure PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (N : ℕ)
    (beta : ℕ → ℝ)
    (halfExtent : ℕ → ℕ) where
  hN : 0 < N
  hbeta : ∀ n, 0 ≤ beta n
  positiveHalfHolonomy :
    ∀ n, PeriodicHypercubicEvenCrossingPlaquetteLabel (halfExtent n) →
      H.HalfConfiguration → Matrix.specialUnitaryGroup (Fin N) ℂ
  crossingKernel_eq_localWilsonProduct :
    ∀ (n : ℕ) (x y : H.HalfConfiguration),
      H.crossingKernel n x y =
        ((periodicHypercubicEvenCrossingPlaquetteList (halfExtent n)).map fun p =>
          localCrossingWilsonKernel N (beta n)
            (positiveHalfHolonomy n p) x y).prod
  halfMeasureFinite : IsFiniteMeasure H.halfMeasure
  amplitude_aestronglyMeasurable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      AEStronglyMeasurable (fun x => H.amplitude n F x) H.halfMeasure
  localFeature_aestronglyMeasurable :
    ∀ (n : ℕ)
      (p : PeriodicHypercubicEvenCrossingPlaquetteLabel (halfExtent n)),
      AEStronglyMeasurable
        (fun x =>
          (localCrossingWilsonKernelConcreteFeature
            N hN (beta n) (hbeta n)
            (positiveHalfHolonomy n p)).feature x)
        H.halfMeasure
  amplitudeBound : ℕ → D.positiveTimeSubalgebra → ℝ
  amplitude_abs_le :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) (x : H.HalfConfiguration),
      |H.amplitude n F x| ≤ amplitudeBound n F

/-- Local one-plaquette feature measurability generates global feature
measurability through the finite completed tensor product; scalar multiplication
then gives the weighted global feature required by the amplitude constructor. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData.toAmplitudeBoundedLocalKernelData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData
      H N beta halfExtent) :
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData
      H N beta halfExtent where
  hN := C.hN
  hbeta := C.hbeta
  positiveHalfHolonomy := C.positiveHalfHolonomy
  crossingKernel_eq_localWilsonProduct :=
    C.crossingKernel_eq_localWilsonProduct
  halfMeasureFinite := C.halfMeasureFinite
  weightedGlobalFeature_aestronglyMeasurable := by
    intro n F
    have hGlobal :
        AEStronglyMeasurable
          (RealHilbertKernelFeature.listProd
            (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
            (fun p =>
              localCrossingWilsonKernel N (beta n)
                (C.positiveHalfHolonomy n p))
            (fun p =>
              localCrossingWilsonKernelConcreteFeature
                N C.hN (beta n) (C.hbeta n)
                  (C.positiveHalfHolonomy n p))).feature
          H.halfMeasure :=
      RealHilbertKernelFeature.listProd_feature_aestronglyMeasurable
        (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
        (fun p =>
          localCrossingWilsonKernel N (beta n)
            (C.positiveHalfHolonomy n p))
        (fun p =>
          localCrossingWilsonKernelConcreteFeature
            N C.hN (beta n) (C.hbeta n)
              (C.positiveHalfHolonomy n p))
        (fun p => C.localFeature_aestronglyMeasurable n p)
    exact AEStronglyMeasurable.smul
      (C.amplitude_aestronglyMeasurable n F)
      hGlobal
  amplitudeBound := C.amplitudeBound
  amplitude_abs_le := C.amplitude_abs_le

/-- Local feature measurability and a scalar amplitude bound imply reflection
positivity at every approximating scale. -/
theorem physical_yang_mills_oriented_evenPeriodicFactoredAmplitudeBoundedLocalKernel_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData
      H N beta halfExtent)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_evenPeriodicAmplitudeBoundedLocalKernel_approximating_reflectionPositive
    G L D H C.toAmplitudeBoundedLocalKernelData n

/-- Local feature measurability and a scalar amplitude bound imply continuum
Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_evenPeriodicFactoredAmplitudeBoundedLocalKernel_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData
      H N beta halfExtent) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_evenPeriodicAmplitudeBoundedLocalKernel_continuum_reflectionPositive
    G L D H C.toAmplitudeBoundedLocalKernelData

end

end MathlibAnalytic
end MGAP4D
