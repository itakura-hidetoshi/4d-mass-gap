import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentPositiveHalfPathBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfAmplitudePathKernel
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance osBoundaryMomentUnfixedPathKernelSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryMomentUnfixedPathKernelSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryMomentUnfixedPathKernelSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryMomentUnfixedPathKernelSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryMomentUnfixedPathKernelSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The fixed-boundary complete unfixed positive-half path-kernel moment with a
retained bulk insertion.  Naming this object gives the downstream boundary
`L²` construction a concrete scalar feature before any transfer-power
specialization. -/
noncomputable def periodicHypercubicEvenBoundaryUnfixedPathKernelMoment
    (H N : ℕ) (beta : ℝ)
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  ∫ x,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)))
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1))) * f x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)

/-- At a fixed shared boundary, the concrete boundary moment is exactly the
finite-volume partition normalization times the complete unfixed positive-half
path-kernel moment with its bulk insertion retained. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_eq_invSqrtPartition_mul_unfixedPathKernelMoment
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryObservableMoment H N hN beta hbeta f b =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        periodicHypercubicEvenBoundaryUnfixedPathKernelMoment H N beta f b := by
  rw [periodicHypercubicEvenBoundaryObservableMoment_eq_invSqrtPartition_mul_osAmplitudeMoment]
  apply congrArg
  unfold periodicHypercubicEvenBoundaryUnfixedPathKernelMoment
  apply integral_congr_ae
  filter_upwards with x
  rw [periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_eq_unfixedPathKernel
    H N hN beta hbeta b x]

/-- For the actual `n`-th approximating Wilson OS carrier, the shared-boundary
moment is therefore a fixed-boundary inserted unfixed path-kernel moment.
No scale-uniform decay or bare-transfer identification is assumed. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_eq_invSqrtPartition_mul_unfixedPathKernelMoment
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration (halfExtent n) N) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta B hInvariant n F b =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
            (beta n) (hbeta n)).base.partitionFunction)⁻¹ *
        periodicHypercubicEvenBoundaryUnfixedPathKernelMoment
          (halfExtent n) N (beta n)
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F) b := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
  exact
    periodicHypercubicEvenBoundaryObservableMoment_eq_invSqrtPartition_mul_unfixedPathKernelMoment
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)
      b

end MathlibAnalytic
end MGAP4D
