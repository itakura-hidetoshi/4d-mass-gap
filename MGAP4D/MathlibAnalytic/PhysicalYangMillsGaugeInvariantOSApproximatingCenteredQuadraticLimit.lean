import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumHalfQuadraticGap
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

/-- The OS quadratic value of a vacuum-centered carrier is the uncentered
quadratic value minus the square of its vacuum expectation. -/
theorem osQuadraticValue_vacuumCenteredCarrier
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.Carrier) :
    P.osQuadraticValue (P.vacuumCenteredCarrier F) =
      P.osQuadraticValue F - (P.omega F.toGaugeInvariant) ^ 2 := by
  calc
    P.osQuadraticValue (P.vacuumCenteredCarrier F) =
        ‖P.vacuumCenteredCarrier F‖ ^ 2 :=
      P.osQuadraticValue_eq_norm_sq (P.vacuumCenteredCarrier F)
    _ = ‖P.physicalState (P.vacuumCenteredCarrier F)‖ ^ 2 := by
      rw [P.norm_physicalState]
    _ = ‖finiteVacuumCentered P.vacuum (P.physicalState F)‖ ^ 2 := by
      rw [P.physicalState_vacuumCenteredCarrier]
    _ = ‖P.physicalState F‖ ^ 2 -
          (inner ℝ P.vacuum (P.physicalState F)) ^ 2 :=
      finite_vacuum_centered_norm_sq
        P.PhysicalHilbert P.vacuum (P.norm_vacuum hP) (P.physicalState F)
    _ = P.osQuadraticValue F - (P.omega F.toGaugeInvariant) ^ 2 := by
      rw [P.norm_physicalState, ← P.osQuadraticValue_eq_norm_sq,
        P.inner_vacuum_physicalState]

namespace PositiveTimeObservableContractionSemigroup

/-- Reflection/time exchange and vacuum fixation imply invariance of the vacuum
expectation under positive-time observable translation. -/
theorem omega_translate_eq
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hExchange : T.ReflectionTimeTranslationExchange)
    (t : NNReal) (F : D.positiveTimeSubalgebra) :
    P.omega
        ((T.translate t F : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      P.omega
        ((F : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) := by
  let Fc := P.carrierOfPositiveTime F
  have hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric :=
    hExchange.toPhysicalSemigroup_isInnerSymmetric
  calc
    P.omega
        ((T.translate t F : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      inner ℝ P.vacuum
        (P.physicalState (P.carrierOfPositiveTime (T.translate t F))) := by
      exact
        (P.inner_vacuum_physicalState
          (P.carrierOfPositiveTime (T.translate t F))).symm
    _ = inner ℝ P.vacuum
        (T.toPhysicalSemigroup.operator t (P.physicalState Fc)) := by
      rw [T.physicalOperator_on_positiveTimeObservable]
    _ = inner ℝ
        (T.toPhysicalSemigroup.operator t (P.physicalState Fc)) P.vacuum :=
      real_inner_comm _ _
    _ = inner ℝ (P.physicalState Fc)
        (T.toPhysicalSemigroup.operator t P.vacuum) :=
      hSymmetric t (P.physicalState Fc) P.vacuum
    _ = inner ℝ (P.physicalState Fc) P.vacuum := by
      rw [T.toPhysicalSemigroup.fixes_vacuum]
    _ = inner ℝ P.vacuum (P.physicalState Fc) :=
      real_inner_comm _ _
    _ = P.omega
        ((F : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :=
      P.inner_vacuum_physicalState Fc

/-- Observable translation commutes with vacuum centering whenever the OS
exchange identity holds. -/
theorem carrierTranslation_vacuumCenteredCarrier
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hExchange : T.ReflectionTimeTranslationExchange)
    (t : NNReal) (F : P.Carrier) :
    T.carrierTranslation t (P.vacuumCenteredCarrier F) =
      P.vacuumCenteredCarrier (T.carrierTranslation t F) := by
  let Fpos := P.positiveTimeElement F
  have homega := T.omega_translate_eq hExchange t Fpos
  unfold vacuumCenteredCarrier
  rw [T.carrierTranslation.map_sub, T.carrierTranslation.map_smul,
    T.carrierTranslation_vacuumObservable]
  apply sub_eq_sub_left.mpr
  rw [T.carrierTranslation_apply]
  change
    P.omega F.toGaugeInvariant • P.vacuumObservable =
      P.omega
        (((T.translate t Fpos : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S)) •
        P.vacuumObservable
  rw [homega]

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- The continuum approximating OS datum is normalized. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant).IsNormalized := by
  change physicalYangMillsContinuumGaugeInvariantWeakStarState S 1 = 1
  rw [physicalYangMillsContinuumGaugeInvariantWeakStarState_apply]
  exact physicalYangMillsContinuumGaugeInvariantExpectation_one S

/-- Vacuum-centered OS quadratic values for one fixed positive-time observable
converge from the actual finite Wilson states to the continuum Wilson state. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_centeredQuadraticValue_tendsto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (F : D.positiveTimeSubalgebra) :
    Tendsto
      (fun n : ℕ =>
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n
        Pn.osQuadraticValue
          (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F)))
      atTop
      (nhds
        (let P∞ :=
          physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant
        P∞.osQuadraticValue
          (P∞.vacuumCenteredCarrier (P∞.carrierOfPositiveTime F)))) := by
  let P∞ :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  have hquadratic :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_osQuadraticValue_tendsto
      S D halfExtent N hN beta hbeta B hInvariant F
  have hexpectation :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp
      (physical_yang_mills_gaugeInvariantWeakStarState_converges S))
      ((F : D.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S)
  have hfinite :
      (fun n : ℕ =>
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n
        Pn.osQuadraticValue
          (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F))) =
      fun n : ℕ =>
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n
        Pn.osQuadraticValue (Pn.carrierOfPositiveTime F) -
          (Pn.omega
            ((F : D.positiveTimeSubalgebra) :
              physicalYangMillsGaugeInvariantObservableSubalgebra S)) ^ 2 := by
    funext n
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    simpa only [Pn.carrierOfPositiveTime_positiveTimeElement] using
      Pn.osQuadraticValue_vacuumCenteredCarrier
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
          S D halfExtent N hN beta hbeta B hInvariant n)
        (Pn.carrierOfPositiveTime F)
  have hcontinuum :
      P∞.osQuadraticValue
          (P∞.vacuumCenteredCarrier (P∞.carrierOfPositiveTime F)) =
        P∞.osQuadraticValue (P∞.carrierOfPositiveTime F) -
          (P∞.omega
            ((F : D.positiveTimeSubalgebra) :
              physicalYangMillsGaugeInvariantObservableSubalgebra S)) ^ 2 := by
    simpa only [P∞.carrierOfPositiveTime_positiveTimeElement] using
      P∞.osQuadraticValue_vacuumCenteredCarrier
        (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
          S D halfExtent N hN beta hbeta B hInvariant)
        (P∞.carrierOfPositiveTime F)
  rw [hfinite, hcontinuum]
  exact hquadratic.sub (hexpectation.pow 2)

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- A finite Wilson half-time OS quadratic gap passes directly to the continuum
centered observable core by weak-star convergence, without finite-Hilbert-space
embeddings into a common carrier. -/
noncomputable def toContinuumHalfQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    (C.toContinuumPositiveTimeObservableContractionSemigroup)
      .HalfQuadraticGapCertificate where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := C.continuum_reflectionTimeTranslationExchange Q.exchange
  core_half_quadratic_decay := by
    intro t F
    let P∞ :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    let T∞ := C.toContinuumPositiveTimeObservableContractionSemigroup
    let Fpos := P∞.positiveTimeElement F
    have hright :=
      physical_yang_mills_evenPeriodicWilsonOS_centeredQuadraticValue_tendsto
        S D halfExtent N hN beta hbeta B hInvariant Fpos
    have hleftBase :=
      physical_yang_mills_evenPeriodicWilsonOS_centeredQuadraticValue_tendsto
        S D halfExtent N hN beta hbeta B hInvariant
        (C.translate (t / 2) Fpos)
    have hleft :
        Tendsto
          (fun n : ℕ =>
            let Pn :=
              physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n
            let Tn := C.toPositiveTimeObservableContractionSemigroup n
            Pn.osQuadraticValue
              (Tn.carrierTranslation (t / 2)
                (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime Fpos))))
          atTop
          (nhds
            (P∞.osQuadraticValue
              (T∞.carrierTranslation (t / 2)
                (P∞.vacuumCenteredCarrier F)))) := by
      have hfiniteFunctions :
          (fun n : ℕ =>
            let Pn :=
              physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n
            let Tn := C.toPositiveTimeObservableContractionSemigroup n
            Pn.osQuadraticValue
              (Tn.carrierTranslation (t / 2)
                (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime Fpos)))) =
          fun n : ℕ =>
            let Pn :=
              physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta B hInvariant n
            Pn.osQuadraticValue
              (Pn.vacuumCenteredCarrier
                (Pn.carrierOfPositiveTime (C.translate (t / 2) Fpos))) := by
        funext n
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n
        let Tn := C.toPositiveTimeObservableContractionSemigroup n
        rw [Tn.carrierTranslation_vacuumCenteredCarrier (Q.exchange n),
          Tn.carrierTranslation_carrierOfPositiveTime]
      have hcontinuumValue :
          P∞.osQuadraticValue
              (T∞.carrierTranslation (t / 2)
                (P∞.vacuumCenteredCarrier F)) =
            P∞.osQuadraticValue
              (P∞.vacuumCenteredCarrier
                (P∞.carrierOfPositiveTime (C.translate (t / 2) Fpos))) := by
        rw [T∞.carrierTranslation_vacuumCenteredCarrier
          (C.continuum_reflectionTimeTranslationExchange Q.exchange),
          T∞.carrierTranslation_apply]
        simp only [Fpos, P∞.carrierOfPositiveTime_positiveTimeElement]
      rw [hfiniteFunctions, hcontinuumValue]
      exact hleftBase
    have hrightScaled :=
      tendsto_const_nhds.mul hright
    have hfinite : ∀ n : ℕ,
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n
        let Tn := C.toPositiveTimeObservableContractionSemigroup n
        Pn.osQuadraticValue
            (Tn.carrierTranslation (t / 2)
              (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime Fpos))) ≤
          Q.quadraticDecayFactor t *
            Pn.osQuadraticValue
              (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime Fpos)) := by
      intro n
      exact Q.finite_half_quadratic_decay n t
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).carrierOfPositiveTime Fpos)
    have hlimit := le_of_tendsto_of_tendsto hleft hrightScaled
      (Eventually.of_forall hfinite)
    simpa only [P∞, T∞, Fpos,
      P∞.carrierOfPositiveTime_positiveTimeElement] using hlimit

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
