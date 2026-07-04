import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringFacade
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The direct façade receipt uses the Prokhorov limit selected by the direct
façade input package. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_prokhorovLimit_eq
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
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).prokhorovLimit =
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K).prokhorovLimit := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput_prokhorovLimit_eq
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The direct façade receipt uses the source observable selected by the direct
façade input package. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_sourceObservable_eq
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
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable =
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput_sourceObservable_eq
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The direct façade receipt uses the target observable selected by the direct
façade input package. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_targetObservable_eq
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
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable =
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput_targetObservable_eq
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The direct façade receipt source observable is the local binary plaquette
observable attached to the explicit source plaquette. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_sourceObservable_eq_plaquetteObservable
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
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable =
      z2InfiniteHypercubicPlaquetteObservable sourcePlaquette := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput.sourceObservable] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput_sourceObservable_eq
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The direct façade receipt target observable is the local binary plaquette
observable attached to the explicit target plaquette. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_targetObservable_eq_plaquetteObservable
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
    (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable =
      z2InfiniteHypercubicPlaquetteObservable targetPlaquette := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput.targetObservable] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt.ofInput_targetObservable_eq
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The input underneath the direct façade receipt remembers its source plaquette. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_input_sourcePlaquette
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
      sourcePlaquette := by
  simpa using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData_sourcePlaquette
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K

/-- The input underneath the direct façade receipt remembers its target plaquette. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_input_targetPlaquette
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
      targetPlaquette := by
  simpa using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData_targetPlaquette
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K

/-- A direct façade API theorem with the source and target observables expanded to
local binary plaquette observables.

This remains a compact infinite-lattice `Z₂` carrier statement under the supplied
all-volume distance hypothesis and finite-volume clustering certificate.  It does
not remove the distance hypothesis and does not assert a Hamiltonian spectral gap
or physical mass gap. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_plaquetteObservable_connectedCorrelation_abs_le
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
        (z2InfiniteHypercubicPlaquetteObservable sourcePlaquette)
        (z2InfiniteHypercubicPlaquetteObservable targetPlaquette)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInputOfData,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput.sourceObservable,
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput.targetObservable] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_connectedCorrelation_abs_le
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K

end

end MathlibAnalytic
end MGAP4D
