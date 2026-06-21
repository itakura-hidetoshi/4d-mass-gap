import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedGibbsFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsWeight
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasurableEquivSymm

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

local instance periodicHypercubicBoundaryDensitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance periodicHypercubicBoundaryDensitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance periodicHypercubicBoundaryDensitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance periodicHypercubicBoundaryDensitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance periodicHypercubicBoundaryDensitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The real value of the transported even-periodic `SU(N)` Wilson Gibbs
density is the normalized Gibbs weight of the geometrically assembled boundary
and two open-half configurations. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta z).toReal =
      Real.exp
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gibbsExponent
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              z.1 z.2.1 z.2.2)) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  change
    (ENNReal.ofReal
      (Real.exp
          (C.base.gibbsExponent
            ((P.boundaryFiberedPiMeasurableEquiv
              (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm z)) /
        C.base.partitionFunction)).toReal =
      Real.exp
          (C.base.gibbsExponent
            (P.boundaryFiberedAssemble z.1 z.2.1 z.2.2)) /
        C.base.partitionFunction
  rw [P.boundaryFiberedPiMeasurableEquiv_symm_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg (Real.exp_pos _).le hZ.le)

/-- Exact factorization of the actual transported Wilson Gibbs density into the
positive and negative open-half amplitudes, the finite product of crossing
plaquette Wilson central functions, and the partition-function normalization.

This is the density-level bridge from the genuine finite-volume Gibbs law to
the local Wilson RKHS product. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_eq_half_half_crossingPlaquette_product_div_partition
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta z).toReal =
      (periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2.1 z.2.2) *
        periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2.1 z.2.2) *
        (∏ p : PeriodicHypercubicEvenCrossingPlaquetteLabel H,
          specialUnitaryWilsonBoltzmannCentralFunction N beta
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                z.1 z.2.1 z.2.2)
              p.1))) /
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal]
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_exp_gibbsExponent_boundaryFibered_eq_half_half_crossingPlaquette_product]

end

end MathlibAnalytic
end MGAP4D
