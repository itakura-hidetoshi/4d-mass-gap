import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumPlaquetteClusteringBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- An interface collecting the continuum-side obligations needed before a
Schwinger-function layer can be routed into an OS-style reconstruction layer. -/
structure ContinuumOSReconstructionInterface
    (C : ContinuumYangMillsConstructionCertificate) where
  localObservablesDischarged : C.axioms.localObservablesAvailable
  schwingerFunctionsDischarged : C.axioms.schwingerFunctionsAvailable
  reflectionPositivityDischarged : C.axioms.reflectionPositivity
  lawPositiveDischarged : C.law.positive
  euclideanInvarianceDischarged : C.law.euclideanInvariant
  gaugeInvarianceDischarged : C.law.gaugeInvariant
  HilbertSpaceCarrier : Type
  vacuumAvailable : Prop
  fieldOperatorMapAvailable : Prop
  hamiltonianAvailable : Prop
  spectralGapStatement : Prop

namespace ContinuumOSReconstructionInterface

/-- The Hilbert-space carrier selected by the OS interface. -/
def HilbertSpace
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) : Type :=
  O.HilbertSpaceCarrier

/-- Reflection positivity is exposed as a proof term. -/
theorem reflectionPositivity
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) :
    C.axioms.reflectionPositivity :=
  O.reflectionPositivityDischarged

/-- Schwinger-function availability is exposed as a proof term. -/
theorem schwingerFunctionsAvailable
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) :
    C.axioms.schwingerFunctionsAvailable :=
  O.schwingerFunctionsDischarged

/-- Local-observable availability is exposed as a proof term. -/
theorem localObservablesAvailable
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) :
    C.axioms.localObservablesAvailable :=
  O.localObservablesDischarged

/-- Euclidean invariance of the continuum law is exposed as a proof term. -/
theorem euclideanInvariance
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) :
    C.law.euclideanInvariant :=
  O.euclideanInvarianceDischarged

/-- Gauge invariance of the continuum law is exposed as a proof term. -/
theorem gaugeInvariance
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) :
    C.law.gaugeInvariant :=
  O.gaugeInvarianceDischarged

/-- The remaining Hamiltonian availability obligation. -/
def hamiltonianObligation
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) : Prop :=
  O.hamiltonianAvailable

/-- The remaining spectral-gap statement obligation. -/
def spectralGapObligation
    {C : ContinuumYangMillsConstructionCertificate}
    (O : ContinuumOSReconstructionInterface C) : Prop :=
  O.spectralGapStatement

end ContinuumOSReconstructionInterface

/-- A handoff from a continuum plaquette-clustering bound certificate to an
OS-style reconstruction interface.

The handoff records that the clustering bound has reached the continuum
Schwinger-function side, while Hamiltonian and spectral-gap obligations remain
separate fields of the OS interface. -/
structure ContinuumPlaquetteClusteringOSReconstructionHandoff
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
      sourcePlaquette targetPlaquette C B T) where
  osInterface : ContinuumOSReconstructionInterface C
  continuumBoundAvailable :
    abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ))
  doesNotCollapseToHamiltonianGap : Prop

namespace ContinuumPlaquetteClusteringOSReconstructionHandoff

/-- Extract the OS interface from the handoff. -/
def interface
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
    (H : ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q) :
    ContinuumOSReconstructionInterface C :=
  H.osInterface

/-- Extract the continuum bound carried by the handoff. -/
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
    (H : ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q) :
    abs (ContinuumPlaquetteClusteringTransferCertificate.continuumConnectedCorrelationValue T) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  H.continuumBoundAvailable

/-- Build an OS handoff from a bound certificate and an OS interface. -/
def ofBoundCertificate
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
    (O : ContinuumOSReconstructionInterface C)
    (doesNotCollapseToHamiltonianGap : Prop) :
    ContinuumPlaquetteClusteringOSReconstructionHandoff beta hBeta distance
      sourcePlaquette targetPlaquette C B T Q :=
  { osInterface := O
    continuumBoundAvailable := ContinuumPlaquetteClusteringBoundCertificate.bound Q
    doesNotCollapseToHamiltonianGap := doesNotCollapseToHamiltonianGap }

end ContinuumPlaquetteClusteringOSReconstructionHandoff

end

end MathlibAnalytic
end MGAP4D
