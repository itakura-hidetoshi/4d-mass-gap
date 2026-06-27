import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHalfQuadraticGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A physical approximating expectation equipped with a direct even-periodic
Wilson pullback bridge is exactly the corresponding finite Gibbs reflected
integral.

This is the equality underlying the existing nonnegativity theorem, separated
out so that quantitative estimates can be transported in either direction. -/
theorem
    physical_yang_mills_evenPeriodicWilsonOS_approximating_expectation_eq_finite_reflectedIntegral
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakLimitBridge
      S halfExtent N hN beta hbeta Q)
    (n : ℕ) :
    (∫ A, Q A ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ A,
        periodicHypercubicEvenFullReflectedObservable
          (halfExtent n) (B.positiveHalfObservable n) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure := by
  rw [B.approximatingMeasure_toMeasure_eq n]
  calc
    (∫ A, Q A
        ∂Measure.map (B.interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure) =
      ∫ A, Q (B.interpolate n A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure := by
      exact MeasureTheory.integral_map
        (B.interpolate_measurable n).aemeasurable
        Q.continuous.aestronglyMeasurable
    _ = ∫ A,
        periodicHypercubicEvenFullReflectedObservable
          (halfExtent n) (B.positiveHalfObservable n) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact B.quadraticObservable_pullback n A

/-- The actual finite-volume reflected Wilson Gibbs integral associated with one
carrier observable of the `n`-th physical approximating OS state. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) : ℝ :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let FB := B.finiteBridge (Pn.positiveTimeElement F)
  ∫ A,
    periodicHypercubicEvenFullReflectedObservable
      (halfExtent n) (FB.positiveHalfObservable n) A
    ∂(periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).gibbsMeasure

/-- The OS quadratic value of an actual approximating physical state is exactly
its finite periodic `SU(N)` Wilson Gibbs reflected integral. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue F =
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Fpos := Pn.positiveTimeElement F
  let FB := B.finiteBridge Fpos
  change
    D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        (Pn.toPositiveTime F) (Pn.toPositiveTime F) = _
  rw [D.osBilinForm_apply]
  change
    physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
        (D.quadraticObservable Fpos) = _
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
    physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  exact
    physical_yang_mills_evenPeriodicWilsonOS_approximating_expectation_eq_finite_reflectedIntegral
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent N hN beta hbeta
      (D.quadraticBoundedContinuousFunction Fpos) FB n

/-- The remaining finite-volume mass-gap input, stated solely as a quantitative
inequality between actual finite periodic `SU(N)` Wilson Gibbs reflected
integrals.

Everything after this inequality is theorem-generated: OS quadratic decay,
reflected bilinear decay, extension from the observable core, Hilbert-space
quadratic decay, transfer-operator norm decay, and finally continuum
Hamiltonian coercivity through the common-carrier bridge. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
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
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) where
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  finite_integral_decay :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)) ≤
          quadraticDecayFactor t *
            physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate

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

/-- A quantitative finite reflected-integral estimate generates the half-time OS
quadratic-gap certificate. -/
noncomputable def toApproximatingHalfQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  finite_half_quadratic_decay := by
    intro n t F
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    rw [physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral,
      physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral]
    exact Q.finite_integral_decay n t F

/-- The finite periodic Wilson Gibbs integral certificate therefore generates the
completed finite-volume transfer-operator norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingHalfQuadraticGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate

end MathlibAnalytic
end MGAP4D

end
