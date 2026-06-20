import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSLocalKernelProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelRKHSFeature

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Concrete scale-dependent Wilson crossing-kernel data.

For each crossing plaquette this structure records only its positive-half
holonomy.  The local Hilbert feature is generated automatically from the exact
`SU(N)` Wilson RKHS feature, so no separate Peter--Weyl coefficient or local
feature assumption remains. -/
structure PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (N : ℕ)
    (beta : ℝ) where
  hN : 0 < N
  hbeta : 0 ≤ beta
  LocalLabel : ℕ → Type
  crossingLabels : ∀ n, List (LocalLabel n)
  positiveHalfHolonomy :
    ∀ n, LocalLabel n →
      H.HalfConfiguration → Matrix.specialUnitaryGroup (Fin N) ℂ
  crossingKernel_eq_localWilsonProduct :
    ∀ (n : ℕ) (x y : H.HalfConfiguration),
      H.crossingKernel n x y =
        ((crossingLabels n).map fun i =>
          localCrossingWilsonKernel N beta
            (positiveHalfHolonomy n i) x y).prod
  weightedGlobalFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun x => H.amplitude n F x •
          (RealHilbertKernelFeature.listProd
            (crossingLabels n)
            (fun i =>
              localCrossingWilsonKernel N beta
                (positiveHalfHolonomy n i))
            (fun i =>
              localCrossingWilsonKernelConcreteFeature
                N hN beta hbeta (positiveHalfHolonomy n i))).feature x)
        H.halfMeasure

/-- Convert concrete crossing holonomies into the existing scale-dependent
local-kernel product certificate.  Every local feature is the exact
Moore--Aronszajn Wilson RKHS feature pulled back along the corresponding
positive-half holonomy. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelData.toLocalKernelProductCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    {N : ℕ}
    {beta : ℝ}
    (C : PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelData
      H N beta) :
    PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H where
  LocalLabel := C.LocalLabel
  crossingLabels := C.crossingLabels
  localKernel := fun n i =>
    localCrossingWilsonKernel N beta (C.positiveHalfHolonomy n i)
  localFeature := fun n i =>
    localCrossingWilsonKernelConcreteFeature
      N C.hN beta C.hbeta (C.positiveHalfHolonomy n i)
  crossingKernel_eq_localProduct :=
    C.crossingKernel_eq_localWilsonProduct
  weightedGlobalFeature_integrable :=
    C.weightedGlobalFeature_integrable

/-- Concrete crossing holonomies and the exact Wilson RKHS feature imply
reflection positivity of every approximating physical lattice state. -/
theorem physical_yang_mills_oriented_concreteLocalKernel_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℝ}
    (C : PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelData
      H N beta)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_localKernelProduct_approximating_reflectionPositive
    G L D H C.toLocalKernelProductCertificate n

/-- Concrete crossing holonomies, exact half-lattice factorization, and the
exact Wilson RKHS feature imply continuum Osterwalder--Schrader reflection
positivity. -/
theorem physical_yang_mills_oriented_concreteLocalKernel_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℝ}
    (C : PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelData
      H N beta) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_localKernelProduct_continuum_reflectionPositive
    G L D H C.toLocalKernelProductCertificate

end

end MathlibAnalytic
end MGAP4D
