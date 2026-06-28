import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelProduct
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorization
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateConstruction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedHaarFactorization
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureMeasurability

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Even-periodic Wilson OS data in which measurability is required only for the
physical scalar amplitude and the positive-half plaquette holonomies.

Continuity of the exact Wilson RKHS feature turns measurable holonomies into
measurable one-plaquette features.  Finite completed tensor products then give
the measurable global feature, and the amplitude bound supplies Bochner
integrability on the finite half-configuration measure. -/
structure PhysicalYangMillsOrientedWilsonOSEvenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernelData
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
  positiveHalfHolonomy_aestronglyMeasurable :
    ∀ (n : ℕ)
      (p : PeriodicHypercubicEvenCrossingPlaquetteLabel (halfExtent n)),
      AEStronglyMeasurable (positiveHalfHolonomy n p) H.halfMeasure
  amplitudeBound : ℕ → D.positiveTimeSubalgebra → ℝ
  amplitude_abs_le :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) (x : H.HalfConfiguration),
      |H.amplitude n F x| ≤ amplitudeBound n F

/-- Measurable positive-half holonomies generate the measurable exact local
Wilson RKHS features required by the factored amplitude constructor. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernelData.toFactoredAmplitudeBoundedLocalKernelData
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernelData
      H N beta halfExtent) :
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData
      H N beta halfExtent where
  hN := C.hN
  hbeta := C.hbeta
  positiveHalfHolonomy := C.positiveHalfHolonomy
  crossingKernel_eq_localWilsonProduct :=
    C.crossingKernel_eq_localWilsonProduct
  halfMeasureFinite := C.halfMeasureFinite
  amplitude_aestronglyMeasurable := C.amplitude_aestronglyMeasurable
  localFeature_aestronglyMeasurable := by
    intro n p
    exact
      localCrossingWilsonKernelConcreteFeature_feature_aestronglyMeasurable
        N C.hN (beta n) (C.hbeta n)
        (C.positiveHalfHolonomy n p)
        (C.positiveHalfHolonomy_aestronglyMeasurable n p)
  amplitudeBound := C.amplitudeBound
  amplitude_abs_le := C.amplitude_abs_le

/-- Measurable positive-half holonomies, measurable amplitudes, and a scalar
amplitude bound imply reflection positivity of every approximating lattice
state. -/
theorem physical_yang_mills_oriented_evenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernel_approximating_reflectionPositive
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernelData
      H N beta halfExtent)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_evenPeriodicFactoredAmplitudeBoundedLocalKernel_approximating_reflectionPositive
    G L D H C.toFactoredAmplitudeBoundedLocalKernelData n

/-- Measurable positive-half holonomies, measurable amplitudes, and a scalar
amplitude bound imply continuum Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_evenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernel_continuum_reflectionPositive
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernelData
      H N beta halfExtent) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_evenPeriodicFactoredAmplitudeBoundedLocalKernel_continuum_reflectionPositive
    G L D H C.toFactoredAmplitudeBoundedLocalKernelData

end

end MathlibAnalytic
end MGAP4D
