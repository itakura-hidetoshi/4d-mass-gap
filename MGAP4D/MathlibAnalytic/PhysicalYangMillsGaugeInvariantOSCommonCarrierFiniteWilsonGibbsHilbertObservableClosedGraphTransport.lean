import MGAP4D.MathlibAnalytic.LinearEquivDecodedObservableRealization
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHilbertEquivalence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransport
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

/-- Finite Wilson graph transport generated from the canonical Gibbs Hilbert
observable decoder.

At every scale, a linear equivalence identifies the abstract finite state space
with the concrete Euclidean Gibbs Hilbert carrier.  Division by `sqrt(mu)` then
recovers a finite Wilson observable, and one linear map realizes that observable
inside the actual positive-time algebra.  Exact represented-state realization
and observable-level time-translation intertwining generate all pointwise graph
observable fields required by the preceding transport layer. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransportData
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
  positiveTimeObservableMap :
    ∀ n,
      ((W.system (F.scale n)).Configuration → ℝ) →ₗ[ℝ]
        D.positiveTimeSubalgebra
  positiveTimeObservableState_eq_embeddedGibbs :
    ∀ n f,
      P.physicalState
          (P.carrierOfPositiveTime (positiveTimeObservableMap n f)) =
        realization.ambientEmbed n
          ((gibbsStateEquiv n).symm
            ((W.system (F.scale n)).gibbsHilbertEmbedLinearMap f))
  positiveTimeObservableTranslationIntertwining :
    ∀ n x t,
      O.translate t
          (positiveTimeObservableMap n
            ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
              (gibbsStateEquiv n x))) =
        positiveTimeObservableMap n
          ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
            (gibbsStateEquiv n
              (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
                (F.hamiltonian n)
                (F.hamiltonianSymmetric n)
                F.StateDimension
                F.stateFinrank
                t x)))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransportData

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

abbrev GibbsHilbertObservableClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- Decode a finite state through the concrete Gibbs Hilbert carrier and realize
it as one actual positive-time observable. -/
noncomputable def stateObservableRealization
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) : F.StateSpace →ₗ[ℝ] D.positiveTimeSubalgebra :=
  decodedObservableRealization
    (R.gibbsStateEquiv n)
    ((W.system (F.scale n)).gibbsHilbertObserveLinearMap)
    (R.positiveTimeObservableMap n)

@[simp] theorem stateObservableRealization_apply
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    R.stateObservableRealization n x =
      R.positiveTimeObservableMap n
        ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
          (R.gibbsStateEquiv n x)) :=
  rfl

/-- The decoded positive-time observable represents the original finite state
exactly in the common continuum carrier. -/
theorem stateObservableRealization_state_eq_ambientEmbed
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    P.physicalState
        (P.carrierOfPositiveTime (R.stateObservableRealization n x)) =
      R.realization.ambientEmbed n x := by
  exact state_decodedObservableRealization_eq
    (e := R.gibbsStateEquiv n)
    (decode := (W.system (F.scale n)).gibbsHilbertObserveLinearMap)
    (encode := (W.system (F.scale n)).gibbsHilbertEmbedLinearMap)
    (realize := R.positiveTimeObservableMap n)
    (state := fun G => P.physicalState (P.carrierOfPositiveTime G))
    (embed := fun y => R.realization.ambientEmbed n y)
    (hEncodeDecode := fun y =>
      finite_lattice_gibbsHilbert_embed_observe
        (W.system (F.scale n)) y)
    (hState := fun f =>
      R.positiveTimeObservableState_eq_embeddedGibbs n f)
    x

/-- Observable-level time-translation intertwining descends to exact represented
state intertwining with the finite spectral semigroup. -/
theorem stateObservableRealization_translationState_eq_ambientSemigroup
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) (t : NNReal) :
    P.physicalState
        (P.carrierOfPositiveTime
          (O.translate t (R.stateObservableRealization n x))) =
      R.realization.ambientEmbed n
        (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          (F.hamiltonian n)
          (F.hamiltonianSymmetric n)
          F.StateDimension
          F.stateFinrank
          t x) := by
  exact state_translate_decodedObservableRealization_eq
    (e := R.gibbsStateEquiv n)
    (decode := (W.system (F.scale n)).gibbsHilbertObserveLinearMap)
    (encode := (W.system (F.scale n)).gibbsHilbertEmbedLinearMap)
    (realize := R.positiveTimeObservableMap n)
    (state := fun G => P.physicalState (P.carrierOfPositiveTime G))
    (embed := fun y => R.realization.ambientEmbed n y)
    (translate := fun s G => O.translate s G)
    (evolve := fun s y =>
      finiteDimensionalSymmetricHamiltonianSpectralSemigroup
        (F.hamiltonian n)
        (F.hamiltonianSymmetric n)
        F.StateDimension
        F.stateFinrank
        s y)
    (hEncodeDecode := fun y =>
      finite_lattice_gibbsHilbert_embed_observe
        (W.system (F.scale n)) y)
    (hState := fun f =>
      R.positiveTimeObservableState_eq_embeddedGibbs n f)
    (hTranslate := by
      intro s y
      simpa [stateObservableRealization] using
        R.positiveTimeObservableTranslationIntertwining n y s)
    t x

/-- Graph observables are generated by applying the single linear realization to
the finite approximation sequence. -/
noncomputable def graphObservable
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    D.positiveTimeSubalgebra :=
  R.stateObservableRealization n (R.finiteApproximation n k m)

/-- The Hamiltonian graph observable is generated by the same linear realization
applied to the finite Hamiltonian image. -/
noncomputable def graphHamiltonianObservable
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    D.positiveTimeSubalgebra :=
  R.stateObservableRealization n
    (F.hamiltonian n (R.finiteApproximation n k m))

/-- Forget the Gibbs Hilbert decoder only after generating the complete finite
spectral-semigroup observable transport package. -/
noncomputable def toSpectralSemigroupObservableClosedGraphTransportData
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData
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
    graphObservable := R.graphObservable
    graphHamiltonianObservable := R.graphHamiltonianObservable
    graphObservableState_eq_embeddedFiniteApproximation := by
      intro n k m
      exact R.stateObservableRealization_state_eq_ambientEmbed n
        (R.finiteApproximation n k m)
    graphObservableTranslationState_eq_embeddedFiniteSemigroup := by
      intro n k m t
      exact R.stateObservableRealization_translationState_eq_ambientSemigroup n
        (R.finiteApproximation n k m) t
    graphHamiltonianObservableState_eq_embeddedHamiltonian := by
      intro n k m
      exact R.stateObservableRealization_state_eq_ambientEmbed n
        (F.hamiltonian n (R.finiteApproximation n k m)) }

/-- Gibbs Hilbert observable realization constructs the closed continuum
Hamiltonian graph transport. -/
noncomputable def toClosedGraphTransportData
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toSpectralSemigroupObservableClosedGraphTransportData.toClosedGraphTransportData

/-- Gibbs Hilbert observable realization supplies the continuum resolvent
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : GibbsHilbertObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toSpectralSemigroupObservableClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Gibbs Hilbert observable realization supplies continuum confluent-resolvent
linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : GibbsHilbertObservableClosedGraphTransportData
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
  R.toSpectralSemigroupObservableClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- The same Gibbs Hilbert observable realization gives positive-power jet
coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : GibbsHilbertObservableClosedGraphTransportData
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
  R.toSpectralSemigroupObservableClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertObservableClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
