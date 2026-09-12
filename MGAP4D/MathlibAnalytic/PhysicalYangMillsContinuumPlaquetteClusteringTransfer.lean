import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeToContinuumGaugeFieldApproximation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A certificate that the named lattice-to-continuum plaquette-clustering bridge
obligations have been discharged.

This structure still does not prove a physical mass gap.  It records that the
source/target plaquette approximation obligations, connected-correlation limit
compatibility, and clustering-bound transfer obligation of a given bridge have
been supplied as proof terms. -/
structure ContinuumPlaquetteClusteringTransferCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) where
  continuumUseDischarged : B.latticeEvidence.continuumUseRequires
  sourceApproximationDischarged : B.sourcePlaquetteApproximatesContinuum
  targetApproximationDischarged : B.targetPlaquetteApproximatesContinuum
  connectedCorrelationLimitDischarged : B.connectedCorrelationLimitCompatible
  clusteringBoundTransferDischarged : B.transfersPlaquetteClusteringBound

namespace ContinuumPlaquetteClusteringTransferCertificate

/-- The source continuum observable selected by a transfer certificate. -/
def sourceContinuumObservable
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (_T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    ContinuumLocalGaugeObservable C.configSpace :=
  LatticePlaquetteToContinuumEvidenceBridge.sourceContinuumObservable B

/-- The target continuum observable selected by a transfer certificate. -/
def targetContinuumObservable
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (_T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    ContinuumLocalGaugeObservable C.configSpace :=
  LatticePlaquetteToContinuumEvidenceBridge.targetContinuumObservable B

/-- The continuum connected correlation selected by a transfer certificate. -/
def continuumConnectedCorrelationValue
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (_T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) : ℝ :=
  LatticePlaquetteToContinuumEvidenceBridge.continuumConnectedCorrelationValue B

/-- A transfer certificate exposes the continuum-use proof term. -/
theorem continuumUse
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    B.latticeEvidence.continuumUseRequires :=
  T.continuumUseDischarged

/-- A transfer certificate exposes the source observable approximation proof. -/
theorem sourceApproximation
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    B.sourcePlaquetteApproximatesContinuum :=
  T.sourceApproximationDischarged

/-- A transfer certificate exposes the target observable approximation proof. -/
theorem targetApproximation
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    B.targetPlaquetteApproximatesContinuum :=
  T.targetApproximationDischarged

/-- A transfer certificate exposes connected-correlation limit compatibility. -/
theorem connectedCorrelationLimitCompatible
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    B.connectedCorrelationLimitCompatible :=
  T.connectedCorrelationLimitDischarged

/-- A transfer certificate exposes the proof that the lattice clustering bound
transfers through the chosen approximation bridge. -/
theorem transfersPlaquetteClusteringBound
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) :
    B.transfersPlaquetteClusteringBound :=
  T.clusteringBoundTransferDischarged

/-- The continuum construction obligation remains explicitly visible even after
a plaquette-clustering transfer certificate has been supplied. -/
def stillRequiresContinuumConstruction
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    {B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C}
    (_T : ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B) : Prop :=
  B.stillRequiresContinuumConstruction

/-- Build a transfer certificate from explicit proof terms for the named bridge
obligations. -/
def ofBridge
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C)
    (hUse : B.latticeEvidence.continuumUseRequires)
    (hSource : B.sourcePlaquetteApproximatesContinuum)
    (hTarget : B.targetPlaquetteApproximatesContinuum)
    (hLimit : B.connectedCorrelationLimitCompatible)
    (hTransfer : B.transfersPlaquetteClusteringBound) :
    ContinuumPlaquetteClusteringTransferCertificate beta hBeta distance
      sourcePlaquette targetPlaquette C B :=
  { continuumUseDischarged := hUse
    sourceApproximationDischarged := hSource
    targetApproximationDischarged := hTarget
    connectedCorrelationLimitDischarged := hLimit
    clusteringBoundTransferDischarged := hTransfer }

end ContinuumPlaquetteClusteringTransferCertificate

end

end MathlibAnalytic
end MGAP4D
