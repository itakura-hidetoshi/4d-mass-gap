import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumOSReconstructionInterface
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A final handoff interface from OS reconstruction data to a spectral-gap
route.

This structure separates the existence of a continuum clustering bound from the
additional Hamiltonian and spectral assertions needed for a mass-gap statement. -/
structure ContinuumMassGapHandoffInterface
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C) where
  hamiltonianDischarged : O.hamiltonianAvailable
  fieldOperatorMapDischarged : O.fieldOperatorMapAvailable
  vacuumDischarged : O.vacuumAvailable
  spectralGapStatementDischarged : O.spectralGapStatement
  positiveGapObligation : Prop
  clusteringBoundFeedsSpectralRoute : Prop
  notDerivedFromPlaquetteBoundAlone : Prop

namespace ContinuumMassGapHandoffInterface

/-- The Hilbert-space carrier selected by the OS layer. -/
def HilbertSpace
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    (_M : ContinuumMassGapHandoffInterface C O) : Type :=
  O.HilbertSpaceCarrier

/-- Hamiltonian availability as a proof term. -/
theorem hamiltonianAvailable
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    (M : ContinuumMassGapHandoffInterface C O) :
    O.hamiltonianAvailable :=
  M.hamiltonianDischarged

/-- Field-operator map availability as a proof term. -/
theorem fieldOperatorMapAvailable
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    (M : ContinuumMassGapHandoffInterface C O) :
    O.fieldOperatorMapAvailable :=
  M.fieldOperatorMapDischarged

/-- The spectral-gap statement supplied by the handoff. -/
theorem spectralGapStatement
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    (M : ContinuumMassGapHandoffInterface C O) :
    O.spectralGapStatement :=
  M.spectralGapStatementDischarged

/-- Positivity of the gap remains a named obligation unless separately supplied. -/
def positiveGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    (M : ContinuumMassGapHandoffInterface C O) : Prop :=
  M.positiveGapObligation

end ContinuumMassGapHandoffInterface

/-- A route object combining a continuum plaquette-clustering OS handoff with a
spectral-gap handoff interface.

This is a routing certificate.  It does not identify the continuum clustering
bound with a Hamiltonian spectral gap by itself. -/
structure ContinuumPlaquetteClusteringToMassGapRoute
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C)
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B)
    (Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T)
    (H : ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q) where
  massGapHandoff : ContinuumMassGapHandoffInterface C H.osInterface
  continuumBoundStillAvailable :
    abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ))
  routeUsesOSInterface : Prop
  routeRequiresSpectralAnalysis : Prop

namespace ContinuumPlaquetteClusteringToMassGapRoute

/-- Extract the continuum clustering bound carried into the route. -/
theorem continuumBound
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    {T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B}
    {Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T}
    {H : ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q}
    (R : ContinuumPlaquetteClusteringToMassGapRoute beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q H) :
    abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  R.continuumBoundStillAvailable

/-- Extract the spectral-gap statement proof term from the route. -/
theorem spectralGapStatement
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    {T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B}
    {Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T}
    {H : ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q}
    (R : ContinuumPlaquetteClusteringToMassGapRoute beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q H) :
    H.osInterface.spectralGapStatement :=
  ContinuumMassGapHandoffInterface.spectralGapStatement R.massGapHandoff

/-- Build a route from an OS handoff and a mass-gap handoff interface. -/
def ofOSHandoff
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C)
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B)
    (Q : ContinuumPlaquetteClusteringBoundCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B T)
    (H : ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q)
    (M : ContinuumMassGapHandoffInterface C H.osInterface)
    (routeUsesOSInterface : Prop)
    (routeRequiresSpectralAnalysis : Prop) :
    ContinuumPlaquetteClusteringToMassGapRoute beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q H :=
  { massGapHandoff := M
    continuumBoundStillAvailable :=
      ContinuumPlaquetteClusteringOSReconstructionHandoff.continuumBound H
    routeUsesOSInterface := routeUsesOSInterface
    routeRequiresSpectralAnalysis := routeRequiresSpectralAnalysis }

end ContinuumPlaquetteClusteringToMassGapRoute

end

end MathlibAnalytic
end MGAP4D
