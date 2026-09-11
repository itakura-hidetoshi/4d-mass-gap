import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteGibbsHeatBathPositiveTimeObservableDilation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransport
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

/-- Finite Wilson graph transport generated from a positive-time observable
dilation of each concrete finite Gibbs heat-bath semigroup.

The carrier-valued finite observable lift and its translation intertwining are no
longer independent fields.  They are generated canonically from the dilation. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathPositiveTimeDilationClosedGraphTransportData
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
  finiteApproximation :
    ℕ → SpectralIndex → ℕ → F.StateSpace
  finiteApproximation_tendsto_selected :
    ∀ n k,
      Tendsto
        (finiteApproximation n k)
        atTop
        (nhds
          ((finiteWitness n).spectralVector (finiteIndexEquiv n k)))
  gibbsStateEquiv :
    ∀ n,
      F.StateSpace ≃ₗ[ℝ]
        (W.system (F.scale n)).GibbsHilbertSpace
  gibbsHamiltonianIntertwining :
    ∀ n x,
      gibbsStateEquiv n (F.hamiltonian n x) =
        (W.system (F.scale n)).gibbsHeatBathHamiltonianLinearMap
          (gibbsStateEquiv n x)
  gibbsSpectralSemigroupIntertwining :
    ∀ n x t,
      gibbsStateEquiv n
          (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
            (F.hamiltonian n)
            (F.hamiltonianSymmetric n)
            F.StateDimension
            F.stateFinrank
            t x) =
        (W.system (F.scale n)).gibbsHeatBathSpectralSemigroup t
          (gibbsStateEquiv n x)
  positiveTimeDilation :
    ∀ n,
      FiniteGibbsHeatBathPositiveTimeObservableDilation
        (W.system (F.scale n)) O
  embeddedVector_tendsto :
    ∀ k,
      Tendsto
        (fun n =>
          A.embed n
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n).physicalState
              (P.carrierRebase
                (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                  S D halfExtent N hN beta hbeta B hInvariant n)
                ((positiveTimeDilation n).carrierMap
                  ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                    (gibbsStateEquiv n
                      ((finiteWitness n).spectralVector
                        (finiteIndexEquiv n k))))))))
        atTop
        (nhds
          ((spectralVector k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
  finiteState_norm :
    ∀ n x,
      ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (P.carrierRebase
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n)
            ((positiveTimeDilation n).carrierMap
              ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                (gibbsStateEquiv n x))))‖ = ‖x‖
  finiteState_orthogonal :
    ∀ n x,
      inner ℝ
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (P.carrierRebase
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n)
            ((positiveTimeDilation n).carrierMap
              ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                (gibbsStateEquiv n x)))))
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta B hInvariant n) = 0
  embed_vacuum :
    ∀ n,
      A.embed n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) =
        P.vacuum
  commonCarrierState_eq :
    ∀ n x,
      P.physicalState
          ((positiveTimeDilation n).carrierMap
            ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
              (gibbsStateEquiv n x))) =
        A.embed n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).physicalState
            (P.carrierRebase
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n)
              ((positiveTimeDilation n).carrierMap
                ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                  (gibbsStateEquiv n x)))))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathPositiveTimeDilationClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathPositiveTimeDilationClosedGraphTransportData

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

abbrev PositiveTimeDilationClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathPositiveTimeDilationClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- Forget the positive-time dilation only after generating the carrier-valued
observable lift and its exact translation intertwining. -/
noncomputable def toObservableLiftClosedGraphTransportData
    (R : PositiveTimeDilationClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap :=
  { finiteWitness := R.finiteWitness
    SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    finiteIndexEquiv := R.finiteIndexEquiv
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    approximateValue_tendsto := R.approximateValue_tendsto
    finiteApproximation := R.finiteApproximation
    finiteApproximation_tendsto_selected :=
      R.finiteApproximation_tendsto_selected
    gibbsStateEquiv := R.gibbsStateEquiv
    gibbsHamiltonianIntertwining := R.gibbsHamiltonianIntertwining
    gibbsSpectralSemigroupIntertwining :=
      R.gibbsSpectralSemigroupIntertwining
    positiveTimeCarrierMap := fun n => (R.positiveTimeDilation n).carrierMap
    embeddedVector_tendsto := R.embeddedVector_tendsto
    finiteState_norm := R.finiteState_norm
    finiteState_orthogonal := R.finiteState_orthogonal
    embed_vacuum := R.embed_vacuum
    commonCarrierState_eq := R.commonCarrierState_eq
    positiveTimeObservableGibbsEvolutionIntertwining := by
      intro n f t
      exact
        (R.positiveTimeDilation n).translate_positiveTimeElement_carrierMap t f }

/-- Positive-time Gibbs dilations construct the concrete Gibbs heat-bath graph
transport package. -/
noncomputable def toGibbsHeatBathObservableClosedGraphTransportData
    (R : PositiveTimeDilationClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap :=
  R.toObservableLiftClosedGraphTransportData
    |>.toGibbsHeatBathObservableClosedGraphTransportData

/-- Positive-time Gibbs dilations construct closed continuum Hamiltonian graph
transport. -/
noncomputable def toClosedGraphTransportData
    (R : PositiveTimeDilationClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toObservableLiftClosedGraphTransportData.toClosedGraphTransportData

/-- Positive-time Gibbs dilations supply the continuum resolvent
approximate-eigenpair package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : PositiveTimeDilationClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toObservableLiftClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Positive-time Gibbs dilations yield continuum confluent-resolvent linear
independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : PositiveTimeDilationClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
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
  R.toObservableLiftClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- Positive-time Gibbs dilations give positive-power jet coefficient-map
faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : PositiveTimeDilationClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
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
  R.toObservableLiftClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathPositiveTimeDilationClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
