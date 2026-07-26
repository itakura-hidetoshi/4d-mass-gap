import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSObservableExponentialHamiltonianDerivative
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonObservableClosedGraphTransport
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

/-- Actual finite Wilson graph transport whose inner positive-time observables
transform as exact exponential eigenmodes under continuum Euclidean-time
translation.

The OS carrier Hamiltonian derivative, the scale-wise graph value, and its
compatibility with the embedded finite Hamiltonian action are theorem-generated.
They are not independent fields. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableEigenactionClosedGraphTransportData
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
  graphObservable :
    ℕ → SpectralIndex → ℕ → D.positiveTimeSubalgebra
  graphObservableTranslationEigenaction :
    ∀ n k m t,
      P.physicalState
          (P.carrierOfPositiveTime
            (O.translate t (graphObservable n k m))) =
        Real.exp
            (-((finiteWitness n).spectralValue (finiteIndexEquiv n k)) *
              (t : ℝ)) •
          P.physicalState
            (P.carrierOfPositiveTime (graphObservable n k m))
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
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableEigenactionClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableEigenactionClosedGraphTransportData

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

abbrev ObservableEigenactionClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableEigenactionClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- The selected finite Wilson Hamiltonian eigenvector. -/
def finiteVector
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The selected finite Wilson Hamiltonian eigenvalue. -/
def finiteEnergy
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite vector embedded in the ambient continuum Hilbert space. -/
noncomputable def ambientEmbeddedVector
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  ((R.realization.excitationEmbed n (R.finiteVector n k) :
      P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)

/-- The theorem-generated OS carrier Hamiltonian derivative of a graph
observable. -/
def graphObservableHamiltonianDerivative
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) : P.Carrier :=
  R.finiteEnergy n k •
    P.carrierOfPositiveTime (R.graphObservable n k m)

/-- The theorem-generated graph value is the finite spectral energy times the
raw embedded finite vector. -/
noncomputable def graphValue
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  R.finiteEnergy n k • R.ambientEmbeddedVector n k

/-- Exact exponential observable eigenaction generates the required carrier
Hamiltonian derivative limit. -/
theorem graphObservableHamiltonianDerivative_tendsto
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    Tendsto
      (O.observableCarrierRightHamiltonianDifferenceQuotient
        (R.graphObservable n k m))
      (nhdsWithin 0 (Ioi 0))
      (nhds (R.graphObservableHamiltonianDerivative n k m)) := by
  exact O.observableCarrierRightHamiltonianDifferenceQuotient_tendsto_of_exponentialEigenaction
    (R.finiteEnergy n k)
    (R.graphObservable n k m)
    (by
      intro t
      simpa [finiteEnergy] using
        R.graphObservableTranslationEigenaction n k m t)

/-- Convergence of graph-observable states automatically gives convergence of
their theorem-generated Hamiltonian derivative states. -/
theorem graphObservableHamiltonianState_tendsto_graphValue
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    Tendsto
      (fun m =>
        P.physicalState (R.graphObservableHamiltonianDerivative n k m))
      atTop (nhds (R.graphValue n k)) := by
  have hmass :
      Tendsto
        (fun _ : ℕ => R.finiteEnergy n k)
        atTop (nhds (R.finiteEnergy n k)) :=
    tendsto_const_nhds
  have hsmul := hmass.smul (R.graphObservableState_tendsto_embedded n k)
  simpa [graphObservableHamiltonianDerivative, graphValue,
    ambientEmbeddedVector,
    ← P.physicalStateLinearMap_apply, map_smul,
    P.physicalStateLinearMap_apply] using hsmul

/-- The theorem-generated graph value is exactly the embedded finite Wilson
Hamiltonian action because the selected finite vector is an eigenvector. -/
theorem graphValue_eq_embeddedHamiltonian
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    R.graphValue n k =
      (((R.realization.excitationEmbed n
          (F.hamiltonian n (R.finiteVector n k)) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) := by
  rw [(R.finiteWitness n).hamiltonian_apply_spectralVector
    (R.finiteIndexEquiv n k)]
  simp [graphValue, ambientEmbeddedVector, finiteEnergy, finiteVector]

/-- Hence scale-wise graph-value compatibility with the finite Hamiltonian is
identically zero rather than an asymptotic input. -/
theorem graphValueCompatibility_tendsto_zero
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        R.graphValue n k -
          (((R.realization.excitationEmbed n
              (F.hamiltonian n (R.finiteVector n k)) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
      atTop (nhds 0) := by
  have hzero : ∀ n : ℕ,
      R.graphValue n k -
          (((R.realization.excitationEmbed n
              (F.hamiltonian n (R.finiteVector n k)) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) = 0 := by
    intro n
    rw [R.graphValue_eq_embeddedHamiltonian n k, sub_self]
  convert
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : P.PhysicalHilbert)) atTop (nhds 0)) using 1
  funext n
  exact hzero n

/-- Forget the exact exponential-eigenaction presentation only after generating
all observable derivative and finite-Hamiltonian graph data. -/
noncomputable def toObservableClosedGraphTransportData
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableClosedGraphTransportData
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
    graphValue := R.graphValue
    graphObservable := R.graphObservable
    graphObservableHamiltonianDerivative :=
      R.graphObservableHamiltonianDerivative
    graphObservableHamiltonianDerivative_tendsto :=
      R.graphObservableHamiltonianDerivative_tendsto
    graphObservableState_tendsto_embedded :=
      R.graphObservableState_tendsto_embedded
    graphObservableHamiltonianState_tendsto_graphValue :=
      R.graphObservableHamiltonianState_tendsto_graphValue
    graphValueCompatibility_tendsto_zero := by
      intro k
      simpa [finiteVector] using R.graphValueCompatibility_tendsto_zero k }

/-- Exact observable eigenaction constructs the closed continuum Hamiltonian
graph transport for selected finite Wilson modes. -/
noncomputable def toClosedGraphTransportData
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toObservableClosedGraphTransportData.toClosedGraphTransportData

/-- Exact observable eigenaction supplies the continuum resolvent approximate
eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : ObservableEigenactionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toObservableClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Exact observable eigenaction supplies continuum confluent-resolvent linear
independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : ObservableEigenactionClosedGraphTransportData
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
  R.toObservableClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- The same exact observable eigenaction gives positive-power jet coefficient
map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : ObservableEigenactionClosedGraphTransportData
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
  R.toObservableClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonObservableEigenactionClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
