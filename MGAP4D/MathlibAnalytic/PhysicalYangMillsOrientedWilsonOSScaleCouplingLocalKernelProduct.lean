import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSLocalKernelProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelRKHSFeature

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Concrete scale-dependent crossing-kernel data with a coupling `beta n` at
lattice scale `n`.  Every local feature is generated from the exact Wilson
RKHS feature at that scale. -/
structure PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (N : ℕ)
    (beta : ℕ → ℝ) where
  hN : 0 < N
  hbeta : ∀ n, 0 ≤ beta n
  LocalLabel : ℕ → Type
  crossingLabels : ∀ n, List (LocalLabel n)
  positiveHalfHolonomy :
    ∀ n, LocalLabel n →
      H.HalfConfiguration → Matrix.specialUnitaryGroup (Fin N) ℂ
  crossingKernel_eq_localWilsonProduct :
    ∀ (n : ℕ) (x y : H.HalfConfiguration),
      H.crossingKernel n x y =
        ((crossingLabels n).map fun i =>
          localCrossingWilsonKernel N (beta n)
            (positiveHalfHolonomy n i) x y).prod
  weightedGlobalFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun x => H.amplitude n F x •
          (RealHilbertKernelFeature.listProd
            (crossingLabels n)
            (fun i =>
              localCrossingWilsonKernel N (beta n)
                (positiveHalfHolonomy n i))
            (fun i =>
              localCrossingWilsonKernelConcreteFeature
                N hN (beta n) (hbeta n) (positiveHalfHolonomy n i))).feature x)
        H.halfMeasure

/-- Forget the concrete scale-dependent Wilson form while retaining the exact
local features and generated tensor-product kernel. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelData.toLocalKernelProductCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    {N : ℕ}
    {beta : ℕ → ℝ}
    (C : PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelData
      H N beta) :
    PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H where
  LocalLabel := C.LocalLabel
  crossingLabels := C.crossingLabels
  localKernel := fun n i =>
    localCrossingWilsonKernel N (beta n) (C.positiveHalfHolonomy n i)
  localFeature := fun n i =>
    localCrossingWilsonKernelConcreteFeature
      N C.hN (beta n) (C.hbeta n) (C.positiveHalfHolonomy n i)
  crossingKernel_eq_localProduct :=
    C.crossingKernel_eq_localWilsonProduct
  weightedGlobalFeature_integrable :=
    C.weightedGlobalFeature_integrable

/-- Scale-dependent Wilson couplings and concrete crossing holonomies imply
reflection positivity of every approximating physical lattice state. -/
theorem physical_yang_mills_oriented_scaleCouplingLocalKernel_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    (C : PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelData
      H N beta)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_localKernelProduct_approximating_reflectionPositive
    G L D H C.toLocalKernelProductCertificate n

/-- Scale-dependent Wilson couplings and exact local RKHS products imply
continuum Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_scaleCouplingLocalKernel_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    (C : PhysicalYangMillsOrientedWilsonOSScaleCouplingLocalKernelData
      H N beta) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_localKernelProduct_continuum_reflectionPositive
    G L D H C.toLocalKernelProductCertificate

end

end MathlibAnalytic
end MGAP4D
