import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousTransport
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

/-- The scalar Bochner moment of a positive-half observable in one fixed
boundary fiber.

Its squared norm is the exact boundary-conditioned Wilson OS quadratic form. -/
noncomputable def periodicHypercubicEvenBoundaryObservableMoment
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryObservableGramFeature
      H N hN beta hbeta f b x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)

/-- The actual full finite-volume Wilson Gibbs reflection integral is exactly the
boundary Haar integral of squared boundary Gram moments.

The proof combines the already formalized boundary-coordinate transport,
orientation-correction transport, and Gram/Bochner factorization. -/
theorem periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryMoment_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (hf : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta (fun x => f x) b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    (∫ A, periodicHypercubicEvenFullReflectedObservable H (fun x => f x) A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ b,
        ‖periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta (fun x => f x) b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  have htransport :
      PeriodicHypercubicEvenWilsonGibbsReflectionTransportData
        H N hN beta hbeta (fun x => f x) := by
    simpa using
      periodicHypercubicEvenWilsonGibbsReflectionTransportData_of_boundedContinuous
        H N hN beta hbeta f
  calc
    (∫ A, periodicHypercubicEvenFullReflectedObservable H (fun x => f x) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ b, ∫ x, ∫ y,
        periodicHypercubicEvenBoundaryWeightedReflectedObservable
          H N hN beta hbeta (fun x => f x) (b, (x, y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) :=
      periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral
        H N hN beta hbeta (fun x => f x) htransport
    _ = ∫ b, ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal *
          (f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      rfl
    _ = ∫ b, ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
          (f x * f y)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) :=
      (periodicHypercubicEvenBoundaryObservable_corrected_boundaryIntegral_eq_original
        H N hN beta hbeta (fun x => f x)).symm
    _ = ∫ b, ‖∫ x,
        periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta (fun x => f x) b x
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) :=
      periodicHypercubicEvenBoundaryObservable_corrected_boundaryIntegral_eq_integral_norm_sq
        H N hN beta hbeta (fun x => f x) hf
    _ = ∫ b,
        ‖periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta (fun x => f x) b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      rfl

/-- The bounded positive-half observable attached to one carrier element of an
actual approximating Wilson OS state. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
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
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) N) ℝ :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  (B.finiteBridge (Pn.positiveTimeElement F)).positiveHalfObservable n

/-- The shared-boundary Gram moment belonging to one carrier element of the
`n`-th actual approximating Wilson OS state. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
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
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) : ℝ :=
  periodicHypercubicEvenBoundaryObservableMoment
    (halfExtent n) N hN (beta n) (hbeta n)
    (fun x =>
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F x)
    b

/-- The finite reflected integral attached to one approximating OS carrier is the
boundary integral of its squared Gram moments. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
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
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hf : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)) :
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  unfold physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
  unfold physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
  exact
    periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryMoment_norm_sq
      (halfExtent n) N hN (beta n) (hbeta n)
      ((B.finiteBridge
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).positiveTimeElement F)).positiveHalfObservable n)
      hf

/-- A scale-uniform finite Wilson mass-gap certificate stated on the shared
boundary Gram moments.

This is a strictly more local input than the full reflected-integral inequality.
All full-configuration integration, boundary-coordinate transport, and Gram
factorization are theorem-generated below. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
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
  gram_integrable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N),
      Integrable
        (periodicHypercubicEvenBoundaryObservableGramFeature
          (halfExtent n) N hN (beta n) (hbeta n)
          (fun x =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F x)
          b)
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
  finite_boundary_moment_decay :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)) b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
        quadraticDecayFactor t *
          ∫ b,
            ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F) b‖ ^ 2
            ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate

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

/-- Boundary-moment decay generates the full finite reflected-integral gap
certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  finite_integral_decay := by
    intro n t
    dsimp only
    intro F
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n
      (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
      (fun b => Q.gram_integrable n
        (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)) b)]
    rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n
      (Pn.vacuumCenteredCarrier F)
      (fun b => Q.gram_integrable n (Pn.vacuumCenteredCarrier F) b)]
    simpa only [Pn, Tn] using Q.finite_boundary_moment_decay n t F

/-- Boundary-moment decay therefore generates the completed finite-volume norm
decay certificate used by the continuum mass-gap route. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate

end MathlibAnalytic
end MGAP4D

end
