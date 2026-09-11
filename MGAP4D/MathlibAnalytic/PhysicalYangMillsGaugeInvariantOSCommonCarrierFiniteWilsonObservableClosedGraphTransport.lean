import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCarrierHamiltonianGeneratorDomain
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonClosedGraphTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Actual finite Wilson common-carrier graph transport presented by
positive-time observables with OS-carrier Hamiltonian derivatives.

Each observable derivative automatically produces a canonical continuum
right-Hamiltonian domain point.  Thus no Hilbert-space graph approximation,
null-space compatibility, quotient descent, or completion lift is supplied as
an independent field.  The remaining actual inputs are the observable
derivative limits themselves and their common-carrier graph convergence. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableClosedGraphTransportData
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (O : P.PositiveTimeObservableContractionSemigroup)
    (hContinuous : O.StrongContinuityOnObservableStates)
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P
        (O.carrierStronglyContinuousPhysicalSemigroup hContinuous) C Q)
    (hSelf : IsSelfAdjoint
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).closedRightHamiltonian)
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) where
  realization :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData
      A F
  finiteWitness :
    (n : ℕ) →
      FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
        F n
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift => sigma.1)
          nodes orderCap
  SpectralIndex : Type
  [spectralFintype : Fintype SpectralIndex]
  finiteIndexEquiv :
    ∀ n, SpectralIndex ≃ (finiteWitness n).SpectralIndex
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralVector : SpectralIndex → P.VacuumOrthogonalHilbert
  approximateValue_tendsto :
    ∀ k,
      Tendsto
        (fun n => (finiteWitness n).spectralValue (finiteIndexEquiv n k))
        atTop (nhds (spectralValue k))
  embeddedVector_tendsto :
    ∀ k,
      Tendsto
        (fun n =>
          realization.excitationEmbed n
            ((finiteWitness n).spectralVector (finiteIndexEquiv n k)))
        atTop (nhds (spectralVector k))
  graphValue : ℕ → SpectralIndex → P.PhysicalHilbert
  graphObservable :
    ℕ → SpectralIndex → ℕ → D.positiveTimeSubalgebra
  graphObservableHamiltonianDerivative :
    ℕ → SpectralIndex → ℕ → P.Carrier
  graphObservableHamiltonianDerivative_tendsto :
    ∀ n k m,
      Tendsto
        (O.observableCarrierRightHamiltonianDifferenceQuotient
          (graphObservable n k m))
        (nhdsWithin 0 (Ioi 0))
        (nhds (graphObservableHamiltonianDerivative n k m))
  graphObservableState_tendsto_embedded :
    ∀ n k,
      Tendsto
        (fun m =>
          P.physicalState
            (P.carrierOfPositiveTime (graphObservable n k m)))
        atTop
        (nhds
          (((realization.excitationEmbed n
              ((finiteWitness n).spectralVector (finiteIndexEquiv n k)) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
  graphObservableHamiltonianState_tendsto_graphValue :
    ∀ n k,
      Tendsto
        (fun m =>
          P.physicalState (graphObservableHamiltonianDerivative n k m))
        atTop (nhds (graphValue n k))
  graphValueCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          graphValue n k -
            (((realization.excitationEmbed n
                (F.hamiltonian n
                  ((finiteWitness n).spectralVector
                    (finiteIndexEquiv n k))) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
        atTop (nhds 0)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableClosedGraphTransportData

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {O : P.PositiveTimeObservableContractionSemigroup}
    {hContinuous : O.StrongContinuityOnObservableStates}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P
        (O.carrierStronglyContinuousPhysicalSemigroup hContinuous) C Q}
    {hSelf : IsSelfAdjoint
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).closedRightHamiltonian}
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    {nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift}
    {orderCap : ℕ}

abbrev ObservableClosedGraphTransportData
    (O : P.PositiveTimeObservableContractionSemigroup)
    (hContinuous : O.StrongContinuityOnObservableStates)
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P
        (O.carrierStronglyContinuousPhysicalSemigroup hContinuous) C Q)
    (hSelf : IsSelfAdjoint
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).closedRightHamiltonian)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- Every differentiable graph observable determines a point of the canonical
continuum right-Hamiltonian domain. -/
noncomputable def graphDomainPoint
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).rightGeneratorDomain :=
  O.rightHamiltonianDomainPointOfObservableDerivative hContinuous
    (R.graphObservable n k m)
    (R.graphObservableHamiltonianDerivative n k m)
    (R.graphObservableHamiltonianDerivative_tendsto n k m)

@[simp] theorem graphDomainPoint_coe
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    ((R.graphDomainPoint n k m :
        (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).rightGeneratorDomain) :
      P.PhysicalHilbert) =
        P.physicalState
          (P.carrierOfPositiveTime (R.graphObservable n k m)) :=
  rfl

/-- The continuum right Hamiltonian of a graph-observable point is its
represented OS carrier derivative. -/
theorem rightHamiltonian_graphDomainPoint
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).rightHamiltonian
        (R.graphDomainPoint n k m) =
      P.physicalState (R.graphObservableHamiltonianDerivative n k m) := by
  exact O.rightHamiltonian_rightHamiltonianDomainPointOfObservableDerivative
    hContinuous
    (R.graphObservable n k m)
    (R.graphObservableHamiltonianDerivative n k m)
    (R.graphObservableHamiltonianDerivative_tendsto n k m)

/-- Forget the observable presentation after automatically constructing the
canonical graph approximations required by closed-graph transport. -/
noncomputable def toClosedGraphTransportData
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  { realization := R.realization
    finiteWitness := R.finiteWitness
    SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    finiteIndexEquiv := R.finiteIndexEquiv
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    approximateValue_tendsto := R.approximateValue_tendsto
    embeddedVector_tendsto := R.embeddedVector_tendsto
    graphValue := R.graphValue
    graphApproximation := R.graphDomainPoint
    graphApproximation_tendsto_embedded := by
      intro n k
      simpa only [R.graphDomainPoint_coe] using
        R.graphObservableState_tendsto_embedded n k
    graphApproximationValue_tendsto_graphValue := by
      intro n k
      simpa only [
        StronglyContinuousPhysicalSemigroup.rightHamiltonianLinearPMap_apply,
        R.rightHamiltonian_graphDomainPoint] using
          R.graphObservableHamiltonianState_tendsto_graphValue n k
    graphValueCompatibility_tendsto_zero :=
      R.graphValueCompatibility_tendsto_zero }

/-- Observable finite Wilson graph transport constructs the continuum resolvent
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Observable-derived finite Wilson graph approximations supply continuum
confluent-resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (hInnerSymmetric :
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).toPhysicalSemigroup.IsInnerSymmetric) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift =>
            A.toVacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
              (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
              hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  R.toClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- The same observable graph transport yields positive-power jet coefficient
map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : ObservableClosedGraphTransportData O hContinuous A hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (hInnerSymmetric :
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous).toPhysicalSemigroup.IsInnerSymmetric)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (hFit : A.toVacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hP hInnerSymmetric hSelf left right :=
  R.toClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
