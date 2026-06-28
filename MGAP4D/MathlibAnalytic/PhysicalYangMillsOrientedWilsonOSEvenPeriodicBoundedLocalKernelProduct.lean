import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelProduct
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Bounded measurable even-periodic crossing-kernel data.

This package replaces the direct Bochner-integrability assumption by the more
primitive inputs used in finite-volume Wilson systems:

* the half-configuration measure is finite;
* the amplitude-weighted exact global RKHS feature is almost-everywhere
  strongly measurable;
* its norm has a uniform finite real bound for each scale and observable.

Mathlib's `Integrable.of_bound` then generates the required integrability. -/
structure PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelData
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
  weightedGlobalFeatureBound :
    ℕ → D.positiveTimeSubalgebra → ℝ
  weightedGlobalFeature_norm_le :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) (x : H.HalfConfiguration),
      ‖H.amplitude n F x •
          (RealHilbertKernelFeature.listProd
            (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
            (fun p =>
              localCrossingWilsonKernel N (beta n)
                (positiveHalfHolonomy n p))
            (fun p =>
              localCrossingWilsonKernelConcreteFeature
                N hN (beta n) (hbeta n) (positiveHalfHolonomy n p))).feature x‖ ≤
        weightedGlobalFeatureBound n F

/-- Generate the direct even-periodic local-kernel certificate.  The only
analytic step is `Integrable.of_bound` on the finite half-configuration
measure. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelData.toEvenPeriodicLocalKernelData
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelData
      H N beta halfExtent) :
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
      H N beta halfExtent where
  hN := C.hN
  hbeta := C.hbeta
  positiveHalfHolonomy := C.positiveHalfHolonomy
  crossingKernel_eq_localWilsonProduct :=
    C.crossingKernel_eq_localWilsonProduct
  weightedGlobalFeature_integrable := by
    intro n F
    letI : IsFiniteMeasure H.halfMeasure := C.halfMeasureFinite
    exact Integrable.of_bound
      (C.weightedGlobalFeature_aestronglyMeasurable n F)
      (C.weightedGlobalFeatureBound n F)
      (Filter.Eventually.of_forall fun x =>
        C.weightedGlobalFeature_norm_le n F x)

/-- Finite-measure bounded measurable local Wilson features imply reflection
positivity of every approximating physical lattice state. -/
theorem physical_yang_mills_oriented_evenPeriodicBoundedLocalKernel_approximating_reflectionPositive
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelData
      H N beta halfExtent)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_evenPeriodicLocalKernel_approximating_reflectionPositive
    G L D H C.toEvenPeriodicLocalKernelData n

/-- Finite-measure bounded measurable local Wilson features imply continuum
Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_evenPeriodicBoundedLocalKernel_continuum_reflectionPositive
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicBoundedLocalKernelData
      H N beta halfExtent) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_evenPeriodicLocalKernel_continuum_reflectionPositive
    G L D H C.toEvenPeriodicLocalKernelData

end

end MathlibAnalytic
end MGAP4D
