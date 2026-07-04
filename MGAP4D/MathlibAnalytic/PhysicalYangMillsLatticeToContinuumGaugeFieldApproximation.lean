import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumGaugeFieldScaffold
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A lattice-to-continuum approximation scheme targeting a continuum `ℝ⁴`
Yang--Mills construction certificate.

This structure does not construct continuum gauge fields.  It names the data and
obligations that must connect lattice carriers to a continuum configuration
space and law. -/
structure LatticeToContinuumGaugeFieldApproximation
    (C : ContinuumYangMillsConstructionCertificate) where
  ApproximationIndex : Type
  latticeSpacing : ApproximationIndex → ℝ
  latticeSpacingPositive : Prop
  latticeSpacingTendsToZero : Prop
  approximatingCarrier : ApproximationIndex → Type
  embedsInContinuumSpacetime : ApproximationIndex → Prop
  approximationProducesConfigurations : Prop
  gaugeSymmetryCompatible : Prop
  continuumLawLimit : Prop

namespace LatticeToContinuumGaugeFieldApproximation

/-- The continuum certificate targeted by an approximation scheme. -/
def targetCertificate
    {C : ContinuumYangMillsConstructionCertificate}
    (_A : LatticeToContinuumGaugeFieldApproximation C) :
    ContinuumYangMillsConstructionCertificate :=
  C

/-- The continuum configuration space targeted by an approximation scheme. -/
def targetConfigSpace
    {C : ContinuumYangMillsConstructionCertificate}
    (_A : LatticeToContinuumGaugeFieldApproximation C) :
    ContinuumGaugeFieldConfigurationSpace :=
  C.configSpace

/-- The continuum law targeted by an approximation scheme. -/
def targetLaw
    {C : ContinuumYangMillsConstructionCertificate}
    (_A : LatticeToContinuumGaugeFieldApproximation C) :
    ContinuumGaugeFieldLaw C.configSpace :=
  C.law

/-- The gauge-compatibility obligation carried by the approximation scheme. -/
def gaugeSymmetryCompatibilityObligation
    {C : ContinuumYangMillsConstructionCertificate}
    (A : LatticeToContinuumGaugeFieldApproximation C) : Prop :=
  A.gaugeSymmetryCompatible

/-- The continuum-law limit obligation carried by the approximation scheme. -/
def continuumLawLimitObligation
    {C : ContinuumYangMillsConstructionCertificate}
    (A : LatticeToContinuumGaugeFieldApproximation C) : Prop :=
  A.continuumLawLimit

end LatticeToContinuumGaugeFieldApproximation

/-- An approximation interface for a lattice observable converging to a continuum
local gauge-invariant observable.

The fields are obligations, not proofs of convergence.  This keeps observable
convergence separate from the already formalized compact infinite-lattice
plaquette-clustering bound. -/
structure LatticeToContinuumLocalObservableApproximation
    (C : ContinuumYangMillsConstructionCertificate)
    (A : LatticeToContinuumGaugeFieldApproximation C) where
  latticeObservableDescriptor : Type
  continuumObservable : ContinuumLocalGaugeObservable C.configSpace
  localityCompatible : Prop
  gaugeInvarianceCompatible : Prop
  expectationConverges : Prop
  connectedCorrelationConvergesWith :
    ContinuumLocalGaugeObservable C.configSpace → Prop

namespace LatticeToContinuumLocalObservableApproximation

/-- The continuum local observable named by an observable-approximation object. -/
def targetObservable
    {C : ContinuumYangMillsConstructionCertificate}
    {A : LatticeToContinuumGaugeFieldApproximation C}
    (O : LatticeToContinuumLocalObservableApproximation C A) :
    ContinuumLocalGaugeObservable C.configSpace :=
  O.continuumObservable

/-- The local-observable gauge-invariance obligation. -/
def gaugeInvarianceObligation
    {C : ContinuumYangMillsConstructionCertificate}
    {A : LatticeToContinuumGaugeFieldApproximation C}
    (O : LatticeToContinuumLocalObservableApproximation C A) : Prop :=
  O.gaugeInvarianceCompatible

/-- The local-observable expectation-convergence obligation. -/
def expectationConvergenceObligation
    {C : ContinuumYangMillsConstructionCertificate}
    {A : LatticeToContinuumGaugeFieldApproximation C}
    (O : LatticeToContinuumLocalObservableApproximation C A) : Prop :=
  O.expectationConverges

end LatticeToContinuumLocalObservableApproximation

/-- A bridge from an already formalized lattice plaquette-clustering evidence
object to a continuum `ℝ⁴` approximation interface.

This is the first typed handoff point from the compact infinite-lattice carrier
to the continuum scaffold.  It records that source and target lattice plaquette
observables must be approximated by continuum local gauge-invariant observables,
and that their connected correlations must converge compatibly with the lattice
bound. -/
structure LatticePlaquetteToContinuumEvidenceBridge
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate) where
  latticeEvidence :
    LatticePlaquetteClusteringEvidenceForContinuum beta hBeta distance
      sourcePlaquette targetPlaquette
  approximation : LatticeToContinuumGaugeFieldApproximation C
  sourceObservableApproximation :
    LatticeToContinuumLocalObservableApproximation C approximation
  targetObservableApproximation :
    LatticeToContinuumLocalObservableApproximation C approximation
  sourcePlaquetteApproximatesContinuum : Prop
  targetPlaquetteApproximatesContinuum : Prop
  connectedCorrelationLimitCompatible : Prop
  transfersPlaquetteClusteringBound : Prop
  stillRequiresContinuumConstruction : Prop

namespace LatticePlaquetteToContinuumEvidenceBridge

/-- The continuum source observable selected by a lattice-to-continuum bridge. -/
def sourceContinuumObservable
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) :
    ContinuumLocalGaugeObservable C.configSpace :=
  B.sourceObservableApproximation.continuumObservable

/-- The continuum target observable selected by a lattice-to-continuum bridge. -/
def targetContinuumObservable
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) :
    ContinuumLocalGaugeObservable C.configSpace :=
  B.targetObservableApproximation.continuumObservable

/-- The continuum connected correlation named by a lattice-to-continuum bridge. -/
def continuumConnectedCorrelationValue
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) : ℝ :=
  continuumConnectedCorrelation C.law
    (sourceContinuumObservable B) (targetContinuumObservable B)

/-- The continuum-use obligation inherited from the lattice evidence. -/
def continuumUseObligation
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) : Prop :=
  B.latticeEvidence.continuumUseRequires

/-- The reflection-positivity obligation still required on the continuum side. -/
def reflectionPositivityObligation
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    (_B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) : Prop :=
  C.axioms.reflectionPositivity

/-- The named obligation saying that the lattice bound has not yet become a
continuum physical mass gap. -/
def continuumConstructionObligation
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    {sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette}
    {C : ContinuumYangMillsConstructionCertificate}
    (B : LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C) : Prop :=
  B.stillRequiresContinuumConstruction

/-- Construct a bridge from explicit evidence, an approximation scheme, and the
named approximation obligations. -/
def ofEvidence
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (C : ContinuumYangMillsConstructionCertificate)
    (E : LatticePlaquetteClusteringEvidenceForContinuum beta hBeta distance
      sourcePlaquette targetPlaquette)
    (A : LatticeToContinuumGaugeFieldApproximation C)
    (sourceApprox : LatticeToContinuumLocalObservableApproximation C A)
    (targetApprox : LatticeToContinuumLocalObservableApproximation C A)
    (sourcePlaquetteApproximatesContinuum : Prop)
    (targetPlaquetteApproximatesContinuum : Prop)
    (connectedCorrelationLimitCompatible : Prop)
    (transfersPlaquetteClusteringBound : Prop)
    (stillRequiresContinuumConstruction : Prop) :
    LatticePlaquetteToContinuumEvidenceBridge beta hBeta distance
      sourcePlaquette targetPlaquette C :=
  { latticeEvidence := E
    approximation := A
    sourceObservableApproximation := sourceApprox
    targetObservableApproximation := targetApprox
    sourcePlaquetteApproximatesContinuum := sourcePlaquetteApproximatesContinuum
    targetPlaquetteApproximatesContinuum := targetPlaquetteApproximatesContinuum
    connectedCorrelationLimitCompatible := connectedCorrelationLimitCompatible
    transfersPlaquetteClusteringBound := transfersPlaquetteClusteringBound
    stillRequiresContinuumConstruction := stillRequiresContinuumConstruction }

end LatticePlaquetteToContinuumEvidenceBridge

end

end MathlibAnalytic
end MGAP4D
