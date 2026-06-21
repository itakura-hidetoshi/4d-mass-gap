import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingWilsonBoltzmannProduct
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeReflection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The genuine even-periodic Wilson Gibbs weight, evaluated on exact
boundary-fibered coordinates, factors into its positive-open-half amplitude,
negative-open-half amplitude, and crossing interaction.  The shared boundary
configuration remains explicit through the assembled full configuration. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_exp_gibbsExponent_boundaryFibered_eq_sector_product
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.gibbsExponent
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)) =
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) *
        periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) *
        periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) := by
  exact
    periodicHypercubicSpecialUnitaryWilsonSystem_exp_gibbsExponent_eq_sector_product
      H N hN beta beta_nonneg
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)

/-- In exact boundary-fibered coordinates, the crossing interaction in the
actual Wilson Gibbs weight is the finite product of the one-plaquette Wilson
central functions. -/
theorem periodicHypercubicEvenCrossingWilsonBoltzmannWeight_boundaryFibered_eq_plaquette_product
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      ∏ p : PeriodicHypercubicEvenCrossingPlaquetteLabel H,
        specialUnitaryWilsonBoltzmannCentralFunction N beta
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
            p.1) := by
  exact
    periodicHypercubicEvenCrossingWilsonBoltzmannWeight_eq_plaquette_product
      H N beta
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)

/-- Fully expanded boundary-fibered form of the genuine finite-volume Wilson
Gibbs weight.  This is the exact algebraic input needed before identifying each
crossing plaquette factor with its positive-half Wilson RKHS kernel. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_exp_gibbsExponent_boundaryFibered_eq_half_half_crossingPlaquette_product
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.gibbsExponent
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)) =
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) *
        periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) *
        (∏ p : PeriodicHypercubicEvenCrossingPlaquetteLabel H,
          specialUnitaryWilsonBoltzmannCentralFunction N beta
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
              p.1)) := by
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_exp_gibbsExponent_boundaryFibered_eq_sector_product]
  rw [periodicHypercubicEvenCrossingWilsonBoltzmannWeight_boundaryFibered_eq_plaquette_product]

end

end MathlibAnalytic
end MGAP4D
