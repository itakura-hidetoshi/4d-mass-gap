import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringReceipt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Build the standard concrete infinite-lattice `Z₂` plaquette clustering input
from explicit arguments.

This is a façade constructor for the compact infinite-lattice binary carrier.  It
only packages existing hypotheses: the positive coupling, the two fixed
integer-lattice plaquettes, the all-volume finite-periodic distance hypothesis,
and the finite-volume uniform spatial-clustering certificate. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput :=
  { beta := beta
    hBeta := hBeta
    distance := distance
    sourcePlaquette := sourcePlaquette
    targetPlaquette := targetPlaquette
    distance_hypothesis := hDistance
    clustering_certificate := K }

/-- The receipt obtained directly from explicit input data. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K) :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The directly packaged receipt satisfies the explicit exponential connected
correlation bound.

This is still only a proof-engineering façade for concrete integer-lattice `Z₂`
plaquette observables on the compact infinite-lattice binary carrier.  It does
not construct a continuum `ℝ⁴` gauge-field configuration space, DLR state,
reflection-positivity limit, OS reconstruction, transfer matrix, Hamiltonian
spectral gap, physical mass gap, or an unconditional proof of the
four-dimensional Yang--Mills mass gap problem. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_connectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
          beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
          beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput_connectedCorrelation_abs_le
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The façade input remembers its source plaquette definitionally. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData_sourcePlaquette
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourcePlaquette =
      sourcePlaquette :=
  rfl

/-- The façade input remembers its target plaquette definitionally. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData_targetPlaquette
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetPlaquette =
      targetPlaquette :=
  rfl

end

end MathlibAnalytic
end MGAP4D
