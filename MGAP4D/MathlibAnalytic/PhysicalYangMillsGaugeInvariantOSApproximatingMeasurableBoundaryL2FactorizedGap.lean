import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2FactorizedGap
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A measurable feature-space factorization package for the finite Wilson
shared-boundary `L²` transfer.

Routine analytic obligations are generated from primitive data:

* open-half Gram integrability follows from finite measure, AE strong
  measurability, and a uniform norm bound;
* shared-boundary `L²` membership follows from AE strong measurability and
  squared-norm integrability.

The remaining model-specific content is an analysis/synthesis factorization,
its exact intertwining with half-time translation, and a uniform bound on the
product of the two operator norms. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate
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
  boundaryMoment_aestronglyMeasurable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      AEStronglyMeasurable
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b)
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryMoment_sq_integrable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      Integrable
        (fun b =>
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2)
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  FeatureState : ℕ → NNReal → Type
  [featureNormedAddCommGroup : ∀ n t,
    NormedAddCommGroup (FeatureState n t)]
  [featureNormedSpace : ∀ n t,
    NormedSpace ℝ (FeatureState n t)]
  analysis :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        FeatureState n t
  synthesis :
    (n : ℕ) → (t : NNReal) →
      FeatureState n t →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (synthesis n t).comp (analysis n t)
            (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)
              ((memLp_two_iff_integrable_sq_norm
                (boundaryMoment_aestronglyMeasurable n
                  (Pn.vacuumCenteredCarrier F))).2
                (boundaryMoment_sq_integrable n
                  (Pn.vacuumCenteredCarrier F)))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            ((memLp_two_iff_integrable_sq_norm
              (boundaryMoment_aestronglyMeasurable n
                (Tn.carrierTranslation (t / 2)
                  (Pn.vacuumCenteredCarrier F)))).2
              (boundaryMoment_sq_integrable n
                (Tn.carrierTranslation (t / 2)
                  (Pn.vacuumCenteredCarrier F))))
  factor_opNorm_mul_le :
    ∀ (n : ℕ) (t : NNReal),
      ‖synthesis n t‖ * ‖analysis n t‖ ≤
        Real.sqrt (quadraticDecayFactor t)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate.featureNormedAddCommGroup
  PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate.featureNormedSpace

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate

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

/-- Generate the boundary-moment `L²` membership required by the factorized
transfer package. -/
theorem boundaryMoment_memLp
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) :=
  (memLp_two_iff_integrable_sq_norm
    (Q.boundaryMoment_aestronglyMeasurable n F)).2
      (Q.boundaryMoment_sq_integrable n F)

/-- Generate the direct feature-space factorization certificate. -/
noncomputable def toApproximatingBoundaryL2FactorizedGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
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
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  FeatureState := Q.FeatureState
  featureNormedAddCommGroup := Q.featureNormedAddCommGroup
  featureNormedSpace := Q.featureNormedSpace
  analysis := Q.analysis
  synthesis := Q.synthesis
  boundaryMoment_intertwining := by
    intro n t
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    intro F
    simpa only [Pn, Tn, boundaryMoment_memLp] using
      Q.boundaryMoment_intertwining n t F
  factor_opNorm_mul_le := Q.factor_opNorm_mul_le

/-- The measurable factorized package supplies the direct boundary-`L²`
transfer-gap certificate. -/
noncomputable def toApproximatingBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2FactorizedGapCertificate
    |>.toApproximatingBoundaryL2TransferGapCertificate

/-- The measurable factorized package supplies the integrated boundary-moment
gap certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2FactorizedGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- The measurable factorized package supplies the completed finite Wilson OS
vacuum-sector norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2FactorizedGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2FactorizedGapCertificate

end MathlibAnalytic
end MGAP4D

end
