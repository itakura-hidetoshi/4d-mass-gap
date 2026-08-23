import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableFiniteIntegralDefectBoundary
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepDerivedRateGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSemigroup
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableWraparoundSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableWraparoundSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableWraparoundSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableWraparoundSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableWraparoundSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableWraparoundSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- On a periodic lattice of side length `L`, displacement by `L` temporal
lattice units is the zero displacement in `ZMod L`. -/
@[simp] theorem periodicHypercubicIntegerTemporalDisplacement_period
    (L : ℕ) :
    periodicHypercubicIntegerTemporalDisplacement L (Int.ofNat L) = 0 := by
  ext mu
  by_cases hmu : mu = (0 : Fin 4)
  · subst mu
    simp [periodicHypercubicIntegerTemporalDisplacement]
  · simp [periodicHypercubicIntegerTemporalDisplacement, hmu]

/-- Consequently one full temporal circuit is literally the identity on finite
periodic configurations. -/
@[simp] theorem periodicHypercubicIntegerTemporalConfigurationTranslation_period_apply
    {Gauge : Type} [MeasurableSpace Gauge]
    (L : ℕ) (A : PeriodicHypercubicEdge L → Gauge) :
    periodicHypercubicIntegerTemporalConfigurationTranslation
        L (Int.ofNat L) A = A := by
  change
    periodicHypercubicConfigurationTranslationMeasurableEquiv L
        (periodicHypercubicIntegerTemporalDisplacement L (Int.ofNat L)) A = A
  rw [periodicHypercubicIntegerTemporalDisplacement_period]
  simpa using
    periodicHypercubicIntegerTemporalConfigurationTranslation_zero_apply L A

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance

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

/-- Although the continuum configuration action need not be periodic globally,
its full-period realizable time acts identically on the image of the actual
finite periodic interpolation. -/
theorem translate_period_interpolate
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ)
    (U : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let L := PeriodicHypercubicEvenSideLength (halfExtent n)
    E.translate (R₀.realizableTime n (Int.ofNat L)) (Q.interpolate n U) =
      Q.interpolate n U := by
  dsimp only
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  have heq :=
    R₀.interpolate_integerTemporal_equivariant n (Int.ofNat L) U
  change
    Q.interpolate n
        (periodicHypercubicIntegerTemporalConfigurationTranslation L
          (Int.ofNat L) U) =
      E.translate (R₀.realizableTime n (Int.ofNat L)) (Q.interpolate n U) at heq
  rw [periodicHypercubicIntegerTemporalConfigurationTranslation_period_apply]
    at heq
  exact heq.symm

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance

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

/-- A full-period realizable observable translation agrees pointwise with the
original observable on every configuration in the finite interpolation image. -/
theorem fullTranslation_period_apply_interpolate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (U : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let L := PeriodicHypercubicEvenSideLength (halfExtent n)
    ((R.fullTranslation n L O :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U) =
      (O : BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U) := by
  dsimp only
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  change
    (O : BoundedContinuousFunction S.Configuration ℝ)
        (E.translate
          (R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat L))
          (Q.interpolate n U)) =
      (O : BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U)
  rw [R.toDiscreteTemporalCovariance.translate_period_interpolate n U]

/-- Therefore the carrier difference between one full periodic circuit and the
original carrier vanishes pointwise on the support-generating interpolation
image of the actual finite Wilson law. -/
theorem realizableCarrierTranslation_period_sub_apply_interpolate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (U : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let L := PeriodicHypercubicEvenSideLength (halfExtent n)
    (((R.realizableCarrierTranslation hInvariant n L F - F).toGaugeInvariant :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U) = 0 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  change
    ((R.positiveTranslation n L (Pn.positiveTimeElement F) :
        D.positiveTimeSubalgebra) :
      BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U) -
      F.observable (Q.interpolate n U) = 0
  rw [sub_eq_zero]
  change
    ((R.fullTranslation n L F.toGaugeInvariant :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U) =
      (F.toGaugeInvariant : BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n U)
  exact R.fullTranslation_period_apply_interpolate n F.toGaugeInvariant U

/-- The full-period carrier difference is an OS null vector for the actual
finite periodic Wilson state.  This is the key wraparound statement: recurrence
is needed only on the finite interpolation image, not globally on the continuum
configuration space. -/
theorem realizableCarrierTranslation_period_sub_norm_eq_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let L := PeriodicHypercubicEvenSideLength (halfExtent n)
    ‖R.realizableCarrierTranslation hInvariant n L F - F‖ = 0 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  let G : Pn.Carrier := R.realizableCarrierTranslation hInvariant n L F - F
  have hpoint : ∀ U : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ,
      (G.toGaugeInvariant : BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n U) = 0 := by
    intro U
    simpa [G, L, Pn] using
      R.realizableCarrierTranslation_period_sub_apply_interpolate
        hInvariant n F U
  have hquad : Pn.osQuadraticValue G = 0 := by
    change
      physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
          (D.reflection G.toGaugeInvariant * G.toGaugeInvariant) = 0
    rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
      physicalYangMillsApproximatingGaugeInvariantExpectation_apply,
      Q.approximatingMeasure_toMeasure_eq n]
    rw [MeasureTheory.integral_map
      (Q.interpolate_measurable n).aemeasurable
      (((D.reflection G.toGaugeInvariant * G.toGaugeInvariant :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ).continuous.aestronglyMeasurable)]
    apply integral_eq_zero_of_ae
    filter_upwards [] with U
    change
      ((D.reflection G.toGaugeInvariant :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n U) *
        (G.toGaugeInvariant : BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n U) = 0
    rw [hpoint U]
    ring
  rw [Pn.osQuadraticValue_eq_norm_sq] at hquad
  change ‖G‖ = 0
  nlinarith [norm_nonneg G]

/-- Full-period recurrence preserves the OS seminorm exactly. -/
theorem realizableCarrierTranslation_period_norm_eq
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let L := PeriodicHypercubicEvenSideLength (halfExtent n)
    ‖R.realizableCarrierTranslation hInvariant n L F‖ = ‖F‖ := by
  dsimp only
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  have hzero :=
    R.realizableCarrierTranslation_period_sub_norm_eq_zero hInvariant n F
  dsimp only at hzero
  have habs :=
    abs_norm_sub_norm_le
      (R.realizableCarrierTranslation hInvariant n L F) F
  rw [hzero] at habs
  exact le_antisymm (by linarith) (by linarith)

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate

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
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {transferFactor : ℕ → ℝ}

/-- Periodic wraparound obstructs any strict global one-step centered contraction
for this literal realizable translation action.  If one centered carrier has
positive OS norm, the one-step factor at that scale cannot be below one.

This theorem is intentionally about the periodic configuration-translation
semigroup `R`.  It does not apply to a genuine slab transfer/conditional kernel,
which need not wrap around as a finite-order automorphism. -/
theorem one_le_transferFactor_of_centered_nonzero
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (hF :
      0 < ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F‖) :
    1 ≤ transferFactor n := by
  by_contra hnot
  have hlt : transferFactor n < 1 := lt_of_not_ge hnot
  have hq0 : 0 ≤ transferFactor n := G.transferFactor_nonneg n
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  have hL : 0 < L := by
    simp [L, PeriodicHypercubicEvenSideLength]
  have hpow : (transferFactor n) ^ L < 1 := by
    exact pow_lt_one₀ hq0 hlt hL
  have hiter := G.centered_norm_le_pow n L F
  dsimp only at hiter
  have hperiod :=
    R.realizableCarrierTranslation_period_norm_eq hInvariant n
      ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)
  dsimp only at hperiod
  rw [hperiod] at hiter
  nlinarith

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate

end MathlibAnalytic
end MGAP4D

end
