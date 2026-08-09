import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizablePositiveTemporalCovariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableSemigroup
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

noncomputable section

open MeasureTheory

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableDiscreteSemigroupSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableDiscreteSemigroupSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableDiscreteSemigroupSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableDiscreteSemigroupSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableDiscreteSemigroupSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableDiscreteSemigroupSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- Realizable physical times add exactly under addition of nonnegative lattice
step counts. -/
theorem realizableTime_ofNat_add
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k l : ℕ) :
    R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat (k + l)) =
      R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k) +
        R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat l) := by
  simp [PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizableTime]
  ring

/-- Zero lattice displacement acts identically on every full gauge-invariant
observable. -/
theorem fullTranslation_zero_apply
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    R.fullTranslation n 0 O = O := by
  apply Subtype.ext
  ext X
  simp only [fullTranslation,
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation,
    physicalGaugeInvariantObservablePrecompAlgEquiv_apply]
  change
    (O : BoundedContinuousFunction S.Configuration ℝ)
        (E.translate
          (R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat 0)) X) =
      (O : BoundedContinuousFunction S.Configuration ℝ) X
  have htime :
      R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat 0) = 0 := by
    simp [PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizableTime]
  rw [htime, E.translate_zero_apply]

/-- Composition of actual full observable translations is exactly addition of
nonnegative lattice step counts. -/
theorem fullTranslation_add_apply
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k l : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    R.fullTranslation n (k + l) O =
      R.fullTranslation n l (R.fullTranslation n k O) := by
  apply Subtype.ext
  ext X
  simp only [fullTranslation,
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation,
    physicalGaugeInvariantObservablePrecompAlgEquiv_apply]
  change
    (O : BoundedContinuousFunction S.Configuration ℝ)
        (E.translate
          (R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat (k + l))) X) =
      (O : BoundedContinuousFunction S.Configuration ℝ)
        (E.translate
          (R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k))
          (E.translate
            (R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat l)) X))
  rw [R.realizableTime_ofNat_add, E.translate_add_apply]

/-- Zero lattice displacement acts identically on the physical positive-time
subalgebra. -/
theorem positiveTranslation_zero_apply
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ) (F : D.positiveTimeSubalgebra) :
    R.positiveTranslation n 0 F = F := by
  apply Subtype.ext
  simpa only [R.positiveTranslation_coe] using
    R.fullTranslation_zero_apply n
      (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)

/-- The realizable positive-time translations form a genuine `ℕ`-indexed
semigroup. -/
theorem positiveTranslation_add_apply
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k l : ℕ) (F : D.positiveTimeSubalgebra) :
    R.positiveTranslation n (k + l) F =
      R.positiveTranslation n l (R.positiveTranslation n k F) := by
  apply Subtype.ext
  simpa only [R.positiveTranslation_coe] using
    R.fullTranslation_add_apply n k l
      (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)

/-- Every realizable positive-time translation is the corresponding iterate of
the actual one-lattice-step translation. -/
theorem positiveTranslation_eq_iterate_one
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ) (F : D.positiveTimeSubalgebra) :
    R.positiveTranslation n k F =
      (fun G : D.positiveTimeSubalgebra => R.positiveTranslation n 1 G)^[k] F := by
  induction k with
  | zero =>
      rw [R.positiveTranslation_zero_apply]
      rfl
  | succ k ih =>
      rw [Nat.succ_eq_add_one, R.positiveTranslation_add_apply, ih,
        Function.iterate_succ_apply']

/-- Actual realizable positive-time translation transported to the finite OS
seminormed carrier.  No boundedness assumption is used at this stage. -/
noncomputable def realizableCarrierTranslation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →ₗ[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  Pn.translateCarrierByPositiveTimeAlgHom (R.positiveTranslation n k)

@[simp] theorem realizableCarrierTranslation_apply
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    R.realizableCarrierTranslation hInvariant n k F =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).carrierOfPositiveTime
          (R.positiveTranslation n k
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).positiveTimeElement F)) :=
  rfl

/-- The carrier action at zero lattice steps is the identity. -/
theorem realizableCarrierTranslation_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    R.realizableCarrierTranslation hInvariant n 0 F = F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    Pn.carrierOfPositiveTime
        (R.positiveTranslation n 0 (Pn.positiveTimeElement F)) = F
  rw [R.positiveTranslation_zero_apply,
    Pn.carrierOfPositiveTime_positiveTimeElement]

/-- Addition of lattice step counts descends exactly to the OS carrier. -/
theorem realizableCarrierTranslation_add
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k l : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    R.realizableCarrierTranslation hInvariant n (k + l) F =
      R.realizableCarrierTranslation hInvariant n l
        (R.realizableCarrierTranslation hInvariant n k F) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    Pn.carrierOfPositiveTime
        (R.positiveTranslation n (k + l) (Pn.positiveTimeElement F)) =
      Pn.carrierOfPositiveTime
        (R.positiveTranslation n l
          (Pn.positiveTimeElement
            (Pn.carrierOfPositiveTime
              (R.positiveTranslation n k (Pn.positiveTimeElement F)))))
  rw [R.positiveTranslation_add_apply,
    Pn.positiveTimeElement_carrierOfPositiveTime]

/-- Every realizable carrier translation fixes the canonical finite OS vacuum
representative because algebra endomorphisms preserve the unit. -/
theorem realizableCarrierTranslation_vacuumObservable
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.realizableCarrierTranslation hInvariant n k Pn.vacuumObservable =
      Pn.vacuumObservable := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    Pn.carrierOfPositiveTime
        (R.positiveTranslation n k (Pn.positiveTimeElement Pn.vacuumObservable)) =
      Pn.vacuumObservable
  have hvac : Pn.positiveTimeElement Pn.vacuumObservable = 1 := by
    rw [← Pn.carrierOfPositiveTime_one]
    exact Pn.positiveTimeElement_carrierOfPositiveTime 1
  rw [hvac, map_one, Pn.carrierOfPositiveTime_one]

/-- The realized discrete carrier translations are symmetric for the finite OS
inner product.  This is theorem-generated from the actual finite state
stationarity and reflection reversal closed in the preceding covariance layer. -/
theorem realizableCarrierTranslation_inner_symmetric
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    inner ℝ (R.realizableCarrierTranslation hInvariant n k F) G =
      inner ℝ F (R.realizableCarrierTranslation hInvariant n k G) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  calc
    inner ℝ (R.realizableCarrierTranslation hInvariant n k F) G =
        D.osBilinForm Pn.omega
          (Pn.toPositiveTime (R.realizableCarrierTranslation hInvariant n k F))
          (Pn.toPositiveTime G) := Pn.inner_eq_osBilinForm _ _
    _ = D.osBilinForm Pn.omega
        (R.positiveTranslation n k (Pn.positiveTimeElement F))
        (Pn.positiveTimeElement G) := by rfl
    _ = D.osBilinForm Pn.omega
        (Pn.positiveTimeElement F)
        (R.positiveTranslation n k (Pn.positiveTimeElement G)) := by
      exact R.osBilinForm_positiveTranslation_exchange n k
        (Pn.positiveTimeElement F) (Pn.positiveTimeElement G)
    _ = D.osBilinForm Pn.omega
        (Pn.toPositiveTime F)
        (Pn.toPositiveTime (R.realizableCarrierTranslation hInvariant n k G)) := by
      rfl
    _ = inner ℝ F (R.realizableCarrierTranslation hInvariant n k G) :=
      (Pn.inner_eq_osBilinForm _ _).symm

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

end MathlibAnalytic
end MGAP4D

end
