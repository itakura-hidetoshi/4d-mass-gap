import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelProduct
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingReflection

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Scale-dependent even-periodic crossing-kernel data.

The local label type and its finite ordered list are no longer assumptions:
at scale `n` they are the concrete crossing plaquettes of side length
`2 (halfExtent n + 1)`. -/
structure PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
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
  weightedGlobalFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
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

/-- Convert the canonical even-periodic labels into the generic
scale-dependent exact Wilson RKHS certificate. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData.toScaleCouplingLocalKernelData
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
      H N beta halfExtent) :
    PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelData
      H N beta where
  hN := C.hN
  hbeta := C.hbeta
  LocalLabel := fun n =>
    PeriodicHypercubicEvenCrossingPlaquetteLabel (halfExtent n)
  crossingLabels := fun n =>
    periodicHypercubicEvenCrossingPlaquetteList (halfExtent n)
  positiveHalfHolonomy := C.positiveHalfHolonomy
  crossingKernel_eq_localWilsonProduct :=
    C.crossingKernel_eq_localWilsonProduct
  weightedGlobalFeature_integrable :=
    C.weightedGlobalFeature_integrable

/-- Canonical even-periodic crossing labels and scale-dependent exact Wilson
RKHS features imply reflection positivity of every lattice approximation. -/
theorem physical_yang_mills_oriented_evenPeriodicLocalKernel_approximating_reflectionPositive
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
      H N beta halfExtent)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_scaleCouplingLocalKernel_approximating_reflectionPositive
    G L D H C.toScaleCouplingLocalKernelData n

/-- Canonical even-periodic crossing labels, the exact kernel product identity,
and weighted-feature integrability imply continuum OS reflection positivity. -/
theorem physical_yang_mills_oriented_evenPeriodicLocalKernel_continuum_reflectionPositive
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
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
      H N beta halfExtent) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_scaleCouplingLocalKernel_continuum_reflectionPositive
    G L D H C.toScaleCouplingLocalKernelData

end

end MathlibAnalytic
end MGAP4D
