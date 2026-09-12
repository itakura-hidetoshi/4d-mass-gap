import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumPlaquetteClusteringTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A conditional certificate carrying the continuum connected-correlation bound
selected by a lattice-to-continuum transfer certificate. -/
structure ContinuumPlaquetteClusteringBoundCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C)
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) where
  continuumConnectedCorrelation_abs_le :
    abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ))

namespace ContinuumPlaquetteClusteringBoundCertificate

/-- The continuum source observable selected by the certificate. -/
def sourceContinuumObservable
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    {T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B}
    (_Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T) :
    ContinuumLocalGaugeObservable C.configSpace :=
  ContinuumPlaquetteClusteringTransferCertificate.sourceContinuumObservable T

/-- The continuum target observable selected by the certificate. -/
def targetContinuumObservable
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    {T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B}
    (_Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T) :
    ContinuumLocalGaugeObservable C.configSpace :=
  ContinuumPlaquetteClusteringTransferCertificate.targetContinuumObservable T

/-- Extract the continuum connected-correlation bound. -/
theorem bound
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    {T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B}
    (Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T) :
    abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  Q.continuumConnectedCorrelation_abs_le

/-- The transfer proof term remains available through the transfer certificate. -/
theorem transfersPlaquetteClusteringBound
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    {T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B}
    (_Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T) :
    B.transfersPlaquetteClusteringBound :=
  ContinuumPlaquetteClusteringTransferCertificate.transfersPlaquetteClusteringBound T

/-- Build a bound certificate from a transfer certificate and the bound proof. -/
def ofTransfer
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C)
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B)
    (hBound :
      abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
        z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
          Real.exp
            (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
              (distance : ℝ))) :
    ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T :=
  { continuumConnectedCorrelation_abs_le := hBound }

end ContinuumPlaquetteClusteringBoundCertificate

end

end MathlibAnalytic
end MGAP4D
