import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricHamiltonianSpectralSemigroup
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

/-- Actual finite Wilson graph transport generated from the theorem-built finite
spectral semigroup.

Each graph observable represents a finite-dimensional approximating state, its
translated observable represents the finite spectral semigroup acting on that
state, and a second positive-time observable represents its finite Hamiltonian
image.  The OS-carrier derivative limit, both graph convergences, and exact
finite-Hamiltonian compatibility are then theorems rather than input fields. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData
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
  graphObservable :
    ℕ → SpectralIndex → ℕ → D.positiveTimeSubalgebra
  graphHamiltonianObservable :
    ℕ → SpectralIndex → ℕ → D.positiveTimeSubalgebra
  graphObservableState_eq_embeddedFiniteApproximation :
    ∀ n k m,
      P.physicalState
          (P.carrierOfPositiveTime (graphObservable n k m)) =
        realization.ambientEmbed n (finiteApproximation n k m)
  graphObservableTranslationState_eq_embeddedFiniteSemigroup :
    ∀ n k m t,
      P.physicalState
          (P.carrierOfPositiveTime
            (O.translate t (graphObservable n k m))) =
        realization.ambientEmbed n
          (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
            (F.hamiltonian n)
            (F.hamiltonianSymmetric n)
            F.StateDimension
            F.stateFinrank
            t
            (finiteApproximation n k m))
  graphHamiltonianObservableState_eq_embeddedHamiltonian :
    ∀ n k m,
      P.physicalState
          (P.carrierOfPositiveTime (graphHamiltonianObservable n k m)) =
        realization.ambientEmbed n
          (F.hamiltonian n (finiteApproximation n k m))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData

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

abbrev SpectralSemigroupObservableClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- The selected finite Wilson Hamiltonian eigenvector. -/
def finiteVector
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The selected finite Wilson Hamiltonian eigenvalue. -/
def finiteEnergy
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite vector in the ambient common carrier. -/
noncomputable def ambientEmbeddedVector
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  R.realization.ambientEmbed n (R.finiteVector n k)

/-- The positive-time observable representative of the finite Hamiltonian image
is the theorem-generated OS-carrier derivative target. -/
def graphObservableHamiltonianDerivative
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) : P.Carrier :=
  P.carrierOfPositiveTime (R.graphHamiltonianObservable n k m)

/-- The graph value is the common-carrier image of the exact finite Hamiltonian
action on the selected limiting finite vector. -/
noncomputable def graphValue
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  R.realization.ambientEmbed n
    (F.hamiltonian n (R.finiteVector n k))

/-- Finite-state convergence and the continuous common-carrier embedding generate
the graph-observable state convergence required by closed-graph transport. -/
theorem graphObservableState_tendsto_embedded
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    Tendsto
      (fun m =>
        P.physicalState
          (P.carrierOfPositiveTime (R.graphObservable n k m)))
      atTop
      (nhds
        (((R.realization.excitationEmbed n (R.finiteVector n k) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))) := by
  have hembed :
      Tendsto
        (fun m => R.realization.ambientEmbed n (R.finiteApproximation n k m))
        atTop
        (nhds (R.realization.ambientEmbed n (R.finiteVector n k))) :=
    ((R.realization.ambientEmbed n).continuous.tendsto (R.finiteVector n k)).comp
      (by
        simpa [finiteVector] using
          R.finiteApproximation_tendsto_selected n k)
  apply hembed.congr'
  exact Filter.Eventually.of_forall fun m =>
    (R.graphObservableState_eq_embeddedFiniteApproximation n k m).symm

/-- The finite spectral-semigroup derivative and the represented-state isometry
generate the OS-carrier Hamiltonian derivative limit. -/
theorem graphObservableHamiltonianDerivative_tendsto
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (m : ℕ) :
    Tendsto
      (O.observableCarrierRightHamiltonianDifferenceQuotient
        (R.graphObservable n k m))
      (nhdsWithin 0 (Ioi 0))
      (nhds (R.graphObservableHamiltonianDerivative n k m)) := by
  rw [P.physicalState_isometry.tendsto_nhds_iff]
  rw [R.graphHamiltonianObservableState_eq_embeddedHamiltonian n k m]
  have hfinite :=
    finiteDimensionalSymmetricHamiltonianSpectralSemigroup_differenceQuotient_tendsto
      (F.hamiltonian n)
      (F.hamiltonianSymmetric n)
      F.StateDimension
      F.stateFinrank
      (R.finiteApproximation n k m)
  have hembed :
      Tendsto
        (fun t : NNReal =>
          R.realization.ambientEmbed n
            ((t : ℝ)⁻¹ •
              (R.finiteApproximation n k m -
                finiteDimensionalSymmetricHamiltonianSpectralSemigroup
                  (F.hamiltonian n)
                  (F.hamiltonianSymmetric n)
                  F.StateDimension
                  F.stateFinrank
                  t
                  (R.finiteApproximation n k m))))
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (R.realization.ambientEmbed n
            (F.hamiltonian n (R.finiteApproximation n k m)))) :=
    ((R.realization.ambientEmbed n).continuous.tendsto
      (F.hamiltonian n (R.finiteApproximation n k m))).comp hfinite
  apply hembed.congr'
  exact Filter.Eventually.of_forall fun t => by
    change
      R.realization.ambientEmbed n
          ((t : ℝ)⁻¹ •
            (R.finiteApproximation n k m -
              finiteDimensionalSymmetricHamiltonianSpectralSemigroup
                (F.hamiltonian n)
                (F.hamiltonianSymmetric n)
                F.StateDimension
                F.stateFinrank
                t
                (R.finiteApproximation n k m))) =
        P.physicalState
          (O.observableCarrierRightHamiltonianDifferenceQuotient
            (R.graphObservable n k m) t)
    rw [O.observableCarrierRightHamiltonianDifferenceQuotient_eq]
    rw [← P.physicalStateLinearMap_apply, map_smul, map_sub,
      P.physicalStateLinearMap_apply, P.physicalStateLinearMap_apply]
    rw [R.graphObservableState_eq_embeddedFiniteApproximation n k m,
      R.graphObservableTranslationState_eq_embeddedFiniteSemigroup n k m t]
    rw [map_smul, map_sub]

/-- Continuity of the finite Hamiltonian and common-carrier embedding generates
convergence of the Hamiltonian-observable states to the exact graph value. -/
theorem graphObservableHamiltonianState_tendsto_graphValue
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    Tendsto
      (fun m =>
        P.physicalState (R.graphObservableHamiltonianDerivative n k m))
      atTop (nhds (R.graphValue n k)) := by
  let Hc : F.StateSpace →L[ℝ] F.StateSpace :=
    LinearMap.toContinuousLinearMap (F.hamiltonian n)
  let K : F.StateSpace →L[ℝ] P.PhysicalHilbert :=
    (R.realization.ambientEmbed n).comp Hc
  have hK :
      Tendsto
        (fun m => K (R.finiteApproximation n k m))
        atTop
        (nhds (K (R.finiteVector n k))) :=
    (K.continuous.tendsto (R.finiteVector n k)).comp
      (by
        simpa [finiteVector] using
          R.finiteApproximation_tendsto_selected n k)
  change Tendsto
    (fun m =>
      P.physicalState
        (P.carrierOfPositiveTime (R.graphHamiltonianObservable n k m)))
    atTop
    (nhds
      (R.realization.ambientEmbed n
        (F.hamiltonian n (R.finiteVector n k))))
  apply hK.congr'
  exact Filter.Eventually.of_forall fun m => by
    change
      R.realization.ambientEmbed n
          (F.hamiltonian n (R.finiteApproximation n k m)) =
        P.physicalState
          (P.carrierOfPositiveTime (R.graphHamiltonianObservable n k m))
    exact
      (R.graphHamiltonianObservableState_eq_embeddedHamiltonian n k m).symm

/-- The graph value is definitionally the embedded finite Wilson Hamiltonian
action, so the scale-wise compatibility defect is identically zero. -/
theorem graphValueCompatibility_tendsto_zero
    (R : SpectralSemigroupObservableClosedGraphTransportData
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
    rfl
  convert
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : P.PhysicalHilbert)) atTop (nhds 0)) using 1
  funext n
  exact hzero n

/-- Forget the finite spectral-semigroup presentation only after generating the
observable derivative and both closed-graph convergence inputs. -/
noncomputable def toObservableClosedGraphTransportData
    (R : SpectralSemigroupObservableClosedGraphTransportData
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
    graphObservableState_tendsto_embedded := by
      intro n k
      simpa [finiteVector] using R.graphObservableState_tendsto_embedded n k
    graphObservableHamiltonianState_tendsto_graphValue :=
      R.graphObservableHamiltonianState_tendsto_graphValue
    graphValueCompatibility_tendsto_zero := by
      intro k
      simpa [finiteVector] using R.graphValueCompatibility_tendsto_zero k }

/-- Finite spectral-semigroup observable transport constructs the closed
continuum Hamiltonian graph transport. -/
noncomputable def toClosedGraphTransportData
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toObservableClosedGraphTransportData.toClosedGraphTransportData

/-- Finite spectral-semigroup observable transport supplies the continuum
resolvent approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : SpectralSemigroupObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toObservableClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Finite spectral-semigroup observable transport supplies continuum
confluent-resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : SpectralSemigroupObservableClosedGraphTransportData
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

/-- The same finite spectral-semigroup transport gives positive-power jet
coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : SpectralSemigroupObservableClosedGraphTransportData
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonSpectralSemigroupObservableClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
