import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteGibbsHeatBathMarkovCompression
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonGibbsHilbertTranslationStateClosedGraphTransport
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCarrierRebase
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

/-- Finite Wilson graph transport generated from a time-zero Markov compression
of each concrete finite Gibbs heat-bath semigroup.

The positive-time lift is not required to intertwine translation pointwise.
Instead, the represented continuum state factors through a time-zero conditional
expectation, whose Markov compression is the finite Gibbs heat-bath spectral
semigroup. This is the standard path-space form of the dilation principle. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathMarkovCompressionClosedGraphTransportData
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
  positiveTimeMarkovCompression :
    ∀ n,
      FiniteGibbsHeatBathPositiveTimeMarkovCompression
        (W.system (F.scale n)) O
  positiveTimeState_factors :
    ∀ n (Fplus : D.positiveTimeSubalgebra.toSubmodule),
      P.physicalState
          (P.carrierOfPositiveTime
            (positiveTimeSubalgebraOfSubmodule Fplus)) =
        A.embed n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).physicalState
            (P.carrierRebase
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n)
              ((positiveTimeMarkovCompression n).carrierMap
                ((positiveTimeMarkovCompression n).condition Fplus))))
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
                ((positiveTimeMarkovCompression n).carrierMap
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
            ((positiveTimeMarkovCompression n).carrierMap
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
            ((positiveTimeMarkovCompression n).carrierMap
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

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathMarkovCompressionClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathMarkovCompressionClosedGraphTransportData

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

abbrev MarkovCompressionClosedGraphTransportData
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathMarkovCompressionClosedGraphTransportData
    O hContinuous A hSelf F nodes orderCap

/-- The carrier-valued finite observable lift generated by the Markov
compression. -/
noncomputable def positiveTimeCarrierMap
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) :
    ((W.system (F.scale n)).Configuration → ℝ) →ₗ[ℝ] P.Carrier :=
  (R.positiveTimeMarkovCompression n).carrierMap

@[simp] theorem positiveTimeCarrierMap_apply
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ)
    (f : (W.system (F.scale n)).Configuration → ℝ) :
    R.positiveTimeCarrierMap n f =
      (R.positiveTimeMarkovCompression n).carrierMap f :=
  rfl

/-- The same lifted observable, rebased into the `n`-th approximating OS
seminormed carrier. -/
noncomputable def finiteCarrierRealization
    (R : MarkovCompressionClosedGraphTransportData
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
    (R : MarkovCompressionClosedGraphTransportData
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
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) : F.StateSpace →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n :=
  (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent N hN beta hbeta B hInvariant n).physicalStateLinearMap.comp
      (R.finiteCarrierRealization n)

@[simp] theorem finiteStateRealizationLinearMap_apply
    (R : MarkovCompressionClosedGraphTransportData
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
    (R : MarkovCompressionClosedGraphTransportData
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
        R.finiteCarrierRealization_apply, R.positiveTimeCarrierMap_apply,
        R.finiteState_norm n x])

@[simp] theorem finiteRealization_apply
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    R.finiteRealization n x =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).physicalState
        (R.finiteCarrierRealization n x) := by
  change R.finiteStateRealizationLinearMap n x = _
  exact R.finiteStateRealizationLinearMap_apply n x

@[simp] theorem finiteRealization_norm
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    ‖R.finiteRealization n x‖ = ‖x‖ := by
  rw [R.finiteRealization_apply, R.finiteCarrierRealization_apply,
    R.positiveTimeCarrierMap_apply, R.finiteState_norm n x]

/-- The Markov-compressed lift constructs the complete finite excitation
realization. -/
noncomputable def toExcitationRealizationData
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData
      A F :=
  { finiteRealization := R.finiteRealization
    finiteRealization_norm := R.finiteRealization_norm
    finiteRealization_orthogonal := by
      intro n x
      rw [R.finiteRealization_apply, R.finiteCarrierRealization_apply,
        R.positiveTimeCarrierMap_apply]
      exact R.finiteState_orthogonal n x
    embed_vacuum := R.embed_vacuum }

/-- The generated excitation embedding has the same ambient representative as
the Markov-compressed lifted observable. -/
@[simp] theorem coe_toExcitationRealizationData_excitationEmbed
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    ((R.toExcitationRealizationData.excitationEmbed n x :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) =
      A.embed n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (R.finiteCarrierRealization n x)) := by
  rw [StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData.coe_excitationEmbed]
  change A.embed n (R.finiteRealization n x) = _
  rw [R.finiteRealization_apply]

/-- Factorization through the time-zero conditional expectation generates the
common-carrier state identity. -/
theorem commonCarrierState_eq
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) :
    P.physicalState
        (R.positiveTimeCarrierMap n
          ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
            (R.gibbsStateEquiv n x))) =
      A.embed n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (R.finiteCarrierRealization n x)) := by
  simpa [positiveTimeCarrierMap, finiteCarrierRealization_apply] using
    (R.positiveTimeMarkovCompression n).physicalState_carrierMap_eq
      (embed := fun f =>
        A.embed n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).physicalState
            (P.carrierRebase
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n)
              ((R.positiveTimeMarkovCompression n).carrierMap f))))
      (R.positiveTimeState_factors n)
      ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
        (R.gibbsStateEquiv n x))

/-- The generated carrier map represents every finite Gibbs observable in the
constructed excitation realization. -/
theorem positiveTimeCarrierState_eq_embeddedGibbs
    (R : MarkovCompressionClosedGraphTransportData
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
            (R.finiteCarrierRealization n x)) :=
      R.commonCarrierState_eq n x
    _ = R.toExcitationRealizationData.ambientEmbed n x := by
      rfl

/-- Decoding commutes with the concrete Gibbs heat-bath spectral semigroup after
the supplied finite-state spectral intertwiner. -/
theorem decodedObservableSpectralSemigroup_eq
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) (t : NNReal) :
    (W.system (F.scale n)).gibbsObservableHeatBathSpectralSemigroup t
        ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
          (R.gibbsStateEquiv n x)) =
      (W.system (F.scale n)).gibbsHilbertObserveLinearMap
        (R.gibbsStateEquiv n
          (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
            (F.hamiltonian n)
            (F.hamiltonianSymmetric n)
            F.StateDimension
            F.stateFinrank
            t x)) := by
  calc
    (W.system (F.scale n)).gibbsObservableHeatBathSpectralSemigroup t
        ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
          (R.gibbsStateEquiv n x)) =
      (W.system (F.scale n)).gibbsHilbertObserveLinearMap
        ((W.system (F.scale n)).gibbsHeatBathSpectralSemigroup t
          (R.gibbsStateEquiv n x)) :=
      finite_lattice_gibbsObservableHeatBathSpectralSemigroup_observe
        (W.system (F.scale n)) t (R.gibbsStateEquiv n x)
    _ = (W.system (F.scale n)).gibbsHilbertObserveLinearMap
        (R.gibbsStateEquiv n
          (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
            (F.hamiltonian n)
            (F.hamiltonianSymmetric n)
            F.StateDimension
            F.stateFinrank
            t x)) := by
      rw [R.gibbsSpectralSemigroupIntertwining n x t]

/-- The Markov compression generates the exact translated represented-state
identity required by the state-level Gibbs Hilbert graph transport. -/
theorem positiveTimeTranslationState_eq_embeddedSemigroup
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap)
    (n : ℕ) (x : F.StateSpace) (t : NNReal) :
    P.physicalState
        (P.carrierOfPositiveTime
          (O.translate t
            (P.positiveTimeElement
              (R.positiveTimeCarrierMap n
                ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                  (R.gibbsStateEquiv n x)))))) =
      R.toExcitationRealizationData.ambientEmbed n
        (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          (F.hamiltonian n)
          (F.hamiltonianSymmetric n)
          F.StateDimension
          F.stateFinrank
          t x) := by
  calc
    P.physicalState
        (P.carrierOfPositiveTime
          (O.translate t
            (P.positiveTimeElement
              (R.positiveTimeCarrierMap n
                ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                  (R.gibbsStateEquiv n x)))))) =
      A.embed n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState
          (P.carrierRebase
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n)
            ((R.positiveTimeMarkovCompression n).carrierMap
              ((W.system (F.scale n)).gibbsObservableHeatBathSpectralSemigroup t
                ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
                  (R.gibbsStateEquiv n x)))))) := by
      simpa [positiveTimeCarrierMap] using
        (R.positiveTimeMarkovCompression n).physicalState_translate_carrierMap_eq
          (embed := fun f =>
            A.embed n
              ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n).physicalState
                (P.carrierRebase
                  (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                    S D halfExtent N hN beta hbeta B hInvariant n)
                  ((R.positiveTimeMarkovCompression n).carrierMap f))))
          (R.positiveTimeState_factors n)
          t
          ((W.system (F.scale n)).gibbsHilbertObserveLinearMap
            (R.gibbsStateEquiv n x))
    _ = R.toExcitationRealizationData.ambientEmbed n
        (finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          (F.hamiltonian n)
          (F.hamiltonianSymmetric n)
          F.StateDimension
          F.stateFinrank
          t x) := by
      rw [R.decodedObservableSpectralSemigroup_eq n x t]
      rfl

/-- Forget the Markov compression only after generating the complete state-level
Gibbs Hilbert graph-transport package. -/
noncomputable def toGibbsHilbertTranslationStateClosedGraphTransportData
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHilbertTranslationStateClosedGraphTransportData
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
      rw [tendsto_subtype_rng]
      simpa only [coe_toExcitationRealizationData_excitationEmbed,
        finiteCarrierRealization_apply, positiveTimeCarrierMap_apply] using
        R.embeddedVector_tendsto k
    finiteApproximation := R.finiteApproximation
    finiteApproximation_tendsto_selected :=
      R.finiteApproximation_tendsto_selected
    gibbsStateEquiv := R.gibbsStateEquiv
    positiveTimeCarrierMap := R.positiveTimeCarrierMap
    positiveTimeCarrierState_eq_embeddedGibbs :=
      R.positiveTimeCarrierState_eq_embeddedGibbs
    positiveTimeTranslationState_eq_embeddedSemigroup :=
      R.positiveTimeTranslationState_eq_embeddedSemigroup }

/-- Markov-compressed finite Gibbs observables construct closed continuum
Hamiltonian graph transport. -/
noncomputable def toClosedGraphTransportData
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    StronglyContinuousPhysicalSemigroup.PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
      A hSelf F nodes orderCap :=
  R.toGibbsHilbertTranslationStateClosedGraphTransportData.toClosedGraphTransportData

/-- The same Markov compression supplies the continuum resolvent
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : MarkovCompressionClosedGraphTransportData
      O hContinuous A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      (O.carrierStronglyContinuousPhysicalSemigroup hContinuous)
      hSelf nodes orderCap :=
  R.toGibbsHilbertTranslationStateClosedGraphTransportData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Markov-compressed finite Gibbs observables yield continuum confluent-resolvent
linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : MarkovCompressionClosedGraphTransportData
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
  R.toGibbsHilbertTranslationStateClosedGraphTransportData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- Markov-compressed finite Gibbs observables give positive-power jet
coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : MarkovCompressionClosedGraphTransportData
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
  R.toGibbsHilbertTranslationStateClosedGraphTransportData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGibbsHeatBathMarkovCompressionClosedGraphTransportData

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
