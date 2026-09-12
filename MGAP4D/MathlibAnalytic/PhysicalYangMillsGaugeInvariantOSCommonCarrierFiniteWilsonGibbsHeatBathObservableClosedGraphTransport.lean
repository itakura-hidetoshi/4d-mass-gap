import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHeatBathSpectralSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransport
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

/-- Finite Wilson graph transport driven by the concrete finite Gibbs heat-bath
evolution.

The abstract finite-state spectral semigroup is identified, scale by scale,
with the spectral semigroup of the actual Gibbs heat-bath Hamiltonian
`sum_e (I - P_e)`.  Positive-time observable translation is required to
intertwine only with the resulting concrete Gibbs observable evolution. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData
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
  positiveTimeCarrierMap :
    ∀ n,
      ((W.system (F.scale n)).Configuration → ℝ) →ₗ[ℝ] P.Carrier
  positiveTimeCarrierState_eq_embeddedGibbs :
    ∀ n f,
      P.physicalState (positiveTimeCarrierMap n f) =
        realization.ambientEmbed n
          ((gibbsStateEquiv n).symm
            ((W.system (F.scale n)).gibbsHilbertEmbedLinearMap f))
  positiveTimeObservableGibbsEvolutionIntertwining :
    ∀ n f t,
      O.translate t
          (P.positiveTimeElement (positiveTimeCarrierMap n f)) =
        P.positiveTimeElement
          (positiveTimeCarrierMap n
            ((W.system (F.scale n)).gibbsObservableHeatBathSpectralSemigroup
              t f))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData

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

abbrev GibbsHeatBathObservableClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- Under the Hamiltonian intertwiner, decoding the abstract finite Hamiltonian
image is exactly the actual observable heat-bath Hamiltonian. -/
theorem decodedHamiltonianObservable_eq_heatBath
    (R : GibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    (W.system (F.scale n)).gibbsHilbertObserveLinearMap
        (R.gibbsStateEquiv n (F.hamiltonian n x)) =
      (W.system (F.scale n)).singleLinkHeatBathHamiltonianObservable
        ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
          (R.gibbsStateEquiv n x)) := by
  rw [R.gibbsHamiltonianIntertwining n x,
    finite_lattice_gibbsHeatBathHamiltonian_observe]

/-- The concrete Gibbs observable evolution and the scale-wise spectral
intertwiner generate the direct abstract-state translation intertwining required
by the preceding Gibbs-Hilbert transport layer. -/
noncomputable def toGibbsHilbertObservableClosedGraphTransportData
    (R : GibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap :=
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
    finiteApproximation := R.finiteApproximation
    finiteApproximation_tendsto_selected :=
      R.finiteApproximation_tendsto_selected
    gibbsStateEquiv := R.gibbsStateEquiv
    positiveTimeCarrierMap := R.positiveTimeCarrierMap
    positiveTimeCarrierState_eq_embeddedGibbs :=
      R.positiveTimeCarrierState_eq_embeddedGibbs
    positiveTimeObservableTranslationIntertwining := by
      intro n x t
      rw [R.positiveTimeObservableGibbsEvolutionIntertwining n
        ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
          (R.gibbsStateEquiv n x)) t]
      apply congrArg P.positiveTimeElement
      apply congrArg (R.positiveTimeCarrierMap n)
      calc
        (W.system (F.scale n)).gibbsObservableHeatBathSpectralSemigroup t
            ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
              (R.gibbsStateEquiv n x)) =
          (W.system (F.scale n)).gibbsHilbertObserveLinearMap
            ((W.system (F.scale n)).gibbsHeatBathSpectralSemigroup t
              (R.gibbsStateEquiv n x)) :=
          finite_lattice_gibbsObservableHeatBathSpectralSemigroup_observe
            (W.system (F.scale n)) t (R.gibbsStateEquiv n x)
        _ =
          (W.system (F.scale n)).gibbsHilbertObserveLinearMap
            (R.gibbsStateEquiv n
              (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
                (F.hamiltonian n)
                (F.hamiltonianSymmetric n)
                F.StateDimension
                F.stateFinrank
                t x)) := by
          rw [R.gibbsSpectralSemigroupIntertwining n x t] }

/-- Concrete finite Gibbs heat-bath evolution constructs the complete finite
spectral-semigroup observable transport package. -/
noncomputable def toSpectralSemigroupObservableClosedGraphTransportData
    (R : GibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap :=
  R.toGibbsHilbertObservableClosedGraphTransportData
    |>.toSpectralSemigroupObservableClosedGraphTransportData

/-- Concrete finite Gibbs heat-bath evolution constructs closed continuum
Hamiltonian graph transport. -/
noncomputable def toClosedGraphTransportData
    (R : GibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toGibbsHilbertObservableClosedGraphTransportData.toClosedGraphTransportData

/-- Concrete finite Gibbs heat-bath evolution supplies the continuum resolvent
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : GibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toGibbsHilbertObservableClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Concrete finite Gibbs heat-bath evolution supplies continuum
confluent-resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : GibbsHeatBathObservableClosedGraphTransportData
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
  R.toGibbsHilbertObservableClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- The same concrete finite Gibbs heat-bath evolution gives positive-power jet
coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : GibbsHeatBathObservableClosedGraphTransportData
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
  R.toGibbsHilbertObservableClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
