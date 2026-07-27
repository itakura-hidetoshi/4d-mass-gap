import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCarrierRebase
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransport
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

/-- Finite Wilson graph transport generated from one common positive-time
observable lift.

The lift lands in the continuum OS carrier, but carrier rebasing presents the
same observable in every approximating Wilson OS seminorm.  Exact finite-state
norm preservation, finite-vacuum orthogonality, and compatibility of the common
carrier embedding then construct the finite excitation realization rather than
accepting it as an independent structure. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransportData
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
                (positiveTimeCarrierMap n
                  ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                    (gibbsStateEquiv n
                      ((finiteWitness n).spectralVector
                        (finiteIndexEquiv n k))))))))
        atTop (nhds ((spectralVector k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
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
  finiteState_norm :
    ∀ n x,
      ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (P.carrierRebase
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n)
            (positiveTimeCarrierMap n
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
            (positiveTimeCarrierMap n
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
          (positiveTimeCarrierMap n
            ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
              (gibbsStateEquiv n x))) =
        A.embed n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).physicalState
            (P.carrierRebase
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n)
              (positiveTimeCarrierMap n
                ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                  (gibbsStateEquiv n x)))))
  positiveTimeObservableGibbsEvolutionIntertwining :
    ∀ n f t,
      O.translate t
          (P.positiveTimeElement (positiveTimeCarrierMap n f)) =
        P.positiveTimeElement
          (positiveTimeCarrierMap n
            ((W.system (F.scale n)).gibbsObservableHeatBathSpectralSemigroup
              t f))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransportData

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

abbrev ObservableLiftClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- The same lifted observable, rebased into the `n`-th approximating OS
seminormed carrier. -/
noncomputable def finiteCarrierRealization
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) : F.StateSpace →ₗ[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier :=
  (P.carrierRebase
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n)).toLinearMap.comp
    ((R.positiveTimeCarrierMap n).comp
      ((W.system (F.scale n)).gibbsHilbertObserveLinearMap.comp
        (R.gibbsStateEquiv n).toLinearMap))

@[simp] theorem finiteCarrierRealization_apply
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    R.finiteCarrierRealization n x =
      P.carrierRebase
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n)
        (R.positiveTimeCarrierMap n
          ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
            (R.gibbsStateEquiv n x))) :=
  rfl

/-- The lifted finite Gibbs state as a linear vector in the actual approximating
Wilson OS Hilbert space. -/
noncomputable def finiteStateRealizationLinearMap
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) : F.StateSpace →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n :=
  (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent N hN beta hbeta B hInvariant n).physicalStateLinearMap.comp
      (R.finiteCarrierRealization n)

@[simp] theorem finiteStateRealizationLinearMap_apply
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    R.finiteStateRealizationLinearMap n x =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).physicalState
        (R.finiteCarrierRealization n x) := by
  rw [finiteStateRealizationLinearMap, LinearMap.comp_apply,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.physicalStateLinearMap_apply]

/-- Exact finite-state norm preservation makes the theorem-generated linear
realization continuous and isometric. -/
noncomputable def finiteRealization
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) : F.StateSpace →L[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n :=
  LinearMap.mkContinuous
    (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := F.StateSpace)
    (F := PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n)
    (σ := RingHom.id ℝ)
    (R.finiteStateRealizationLinearMap n)
    1
    (by
      intro x
      rw [one_mul, R.finiteStateRealizationLinearMap_apply,
        R.finiteCarrierRealization_apply, R.finiteState_norm n x])

@[simp] theorem finiteRealization_norm
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    ‖R.finiteRealization n x‖ = ‖x‖ := by
  change ‖R.finiteStateRealizationLinearMap n x‖ = ‖x‖
  rw [R.finiteStateRealizationLinearMap_apply,
    R.finiteCarrierRealization_apply, R.finiteState_norm n x]

/-- The common observable lift constructs the complete finite excitation
realization required by the preceding transport layers. -/
noncomputable def toExcitationRealizationData
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData
      A F :=
  { finiteRealization := R.finiteRealization
    finiteRealization_norm := R.finiteRealization_norm
    finiteRealization_orthogonal := by
      intro n x
      change inner ℝ
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (R.finiteCarrierRealization n x))
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta B hInvariant n) = 0
      rw [R.finiteCarrierRealization_apply]
      exact R.finiteState_orthogonal n x
    embed_vacuum := R.embed_vacuum }

/-- Compatibility of the common-carrier embedding with the same lifted
observable generates the represented-state identity required by PR #1173. -/
theorem positiveTimeCarrierState_eq_embeddedGibbs
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ)
    (f : (W.system (F.scale n)).Configuration → ℝ) :
    P.physicalState (R.positiveTimeCarrierMap n f) =
      R.toExcitationRealizationData.ambientEmbed n
        ((R.gibbsStateEquiv n).symm
          ((W.system (F.scale n)).gibbsHilbertEmbedLinearMap f)) := by
  let x : F.StateSpace :=
    (R.gibbsStateEquiv n).symm
      ((W.system (F.scale n)).gibbsHilbertEmbedLinearMap f)
  have hx :
      (W.system (F.scale n)).gibbsHilbertObserveLinearMap
          (R.gibbsStateEquiv n x) = f := by
    dsimp [x]
    rw [LinearEquiv.apply_symm_apply,
      finite_lattice_gibbsHilbert_observe_embed]
  calc
    P.physicalState (R.positiveTimeCarrierMap n f) =
        P.physicalState
          (R.positiveTimeCarrierMap n
            ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
              (R.gibbsStateEquiv n x))) := by rw [hx]
    _ = A.embed n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).physicalState
            (P.carrierRebase
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n)
              (R.positiveTimeCarrierMap n
                ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                  (R.gibbsStateEquiv n x))))) :=
      R.commonCarrierState_eq n x
    _ = R.toExcitationRealizationData.ambientEmbed n x := by
      rfl

/-- Forget the carrier-rebase construction only after generating the full
concrete finite Gibbs heat-bath graph-transport package. -/
noncomputable def toGibbsHeatBathObservableClosedGraphTransportData
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap :=
  { realization := R.toExcitationRealizationData
    finiteWitness := R.finiteWitness
    SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    finiteIndexEquiv := R.finiteIndexEquiv
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    approximateValue_tendsto := R.approximateValue_tendsto
    embeddedVector_tendsto := by
      intro k
      simpa [StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData.coe_excitationEmbed,
        toExcitationRealizationData, finiteRealization,
        finiteStateRealizationLinearMap, finiteCarrierRealization] using
        R.embeddedVector_tendsto k
    finiteApproximation := R.finiteApproximation
    finiteApproximation_tendsto_selected :=
      R.finiteApproximation_tendsto_selected
    gibbsStateEquiv := R.gibbsStateEquiv
    gibbsHamiltonianIntertwining := R.gibbsHamiltonianIntertwining
    gibbsSpectralSemigroupIntertwining :=
      R.gibbsSpectralSemigroupIntertwining
    positiveTimeCarrierMap := R.positiveTimeCarrierMap
    positiveTimeCarrierState_eq_embeddedGibbs :=
      R.positiveTimeCarrierState_eq_embeddedGibbs
    positiveTimeObservableGibbsEvolutionIntertwining :=
      R.positiveTimeObservableGibbsEvolutionIntertwining }

/-- One common positive-time observable lift constructs the closed continuum
Hamiltonian graph transport. -/
noncomputable def toClosedGraphTransportData
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toGibbsHeatBathObservableClosedGraphTransportData.toClosedGraphTransportData

/-- The same lift supplies the continuum resolvent approximate-eigenpair package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : ObservableLiftClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toGibbsHeatBathObservableClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- The observable lift yields continuum confluent-resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : ObservableLiftClosedGraphTransportData
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
  R.toGibbsHeatBathObservableClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- The observable lift gives positive-power jet coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : ObservableLiftClosedGraphTransportData
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
  R.toGibbsHeatBathObservableClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathObservableLiftClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
