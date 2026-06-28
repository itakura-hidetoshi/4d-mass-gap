import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryMomentGap
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance boundedBoundaryMomentSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- A boundary-moment mass-gap certificate whose Gram-feature integrability is
not postulated directly.

For every finite lattice scale and fixed shared-boundary configuration, this
package asks only for:

* finiteness of the open-half Haar measure;
* almost-everywhere strong measurability of the scalar Gram feature;
* a uniform finite real bound for its norm.

Mathlib's `Integrable.of_bound` then generates the Bochner integrability needed
by the exact boundary Gram factorization.  The remaining quantitative input is
the scale-uniform boundary-moment decay itself. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundedBoundaryMomentGapCertificate
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
  openHalfMeasureFinite : ∀ n,
    IsFiniteMeasure
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
  gramFeature_aestronglyMeasurable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N),
      AEStronglyMeasurable
        (periodicHypercubicEvenBoundaryObservableGramFeature
          (halfExtent n) N hN (beta n) (hbeta n)
          (fun x =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F x)
          b)
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
  gramFeatureBound :
    (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N → ℝ
  gramFeature_norm_le :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N)
      (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) N),
      ‖periodicHypercubicEvenBoundaryObservableGramFeature
          (halfExtent n) N hN (beta n) (hbeta n)
          (fun y =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F y)
          b x‖ ≤ gramFeatureBound n F b
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundedBoundaryMomentGapCertificate

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

/-- Bounded measurable boundary Gram features generate the direct boundary-moment
certificate by `Integrable.of_bound` on each finite open-half Haar measure. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundedBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  gram_integrable := by
    intro n F b
    letI : IsFiniteMeasure
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
      Q.openHalfMeasureFinite n
    exact Integrable.of_bound
      (Q.gramFeature_aestronglyMeasurable n F b)
      (Q.gramFeatureBound n F b)
      (Filter.Eventually.of_forall fun x =>
        Q.gramFeature_norm_le n F b x)
  finite_boundary_moment_decay := Q.finite_boundary_moment_decay

/-- The bounded boundary-feature package therefore supplies the finite reflected
Wilson integral gap certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundedBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryMomentGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- The bounded boundary-feature package also supplies the completed finite
Wilson OS vacuum-sector norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundedBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryMomentGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundedBoundaryMomentGapCertificate

end MathlibAnalytic
end MGAP4D

end
