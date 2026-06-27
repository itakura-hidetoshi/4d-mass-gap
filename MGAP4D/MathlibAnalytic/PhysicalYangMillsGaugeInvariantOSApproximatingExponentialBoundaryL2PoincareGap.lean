import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingMeasurableBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A finite Wilson shared-boundary Poincaré package with the concrete
exponential defect

`δ(t) = 1 - exp (-mass * t)`.

Unlike the general Poincaré package, this structure does not ask for a separate
small-time slope proof.  Positivity and boundedness of the defect and the exact
right-time slope are generated from `mass_pos` by the exponential calculus
lemmas in `PhysicalYangMillsGaugeInvariantOSExponentialGapSlope`.

The remaining quantitative input is the scale-uniform Wilson boundary estimate

`(1 - exp (-mass * t)) ‖v‖² ≤ ‖v‖² - ‖K_{n,t} v‖²`.
-/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
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
  boundaryTransfer :
    (n : ℕ) → NNReal →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        boundaryTransfer n t
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
  boundaryTransfer_exponential_defect_bound :
    ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
        (halfExtent n) N),
      (1 - Real.exp (-mass * (t : ℝ))) * ‖v‖ ^ 2 ≤
        ‖v‖ ^ 2 - ‖boundaryTransfer n t v‖ ^ 2

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

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

/-- Generate the general measurable Poincaré certificate with exponential
defect and automatically verified positive small-time slope. -/
noncomputable def toApproximatingMeasurableBoundaryL2PoincareGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  defectFactor := fun t => 1 - Real.exp (-Q.mass * (t : ℝ))
  defectFactor_nonneg :=
    exponential_defect_nonneg Q.mass_pos.le
  defectFactor_le_one :=
    exponential_defect_le_one Q.mass
  slope_tendsto := by
    simpa only [sub_sub_cancel] using
      exponential_quadraticDecayFactor_slope_tendsto Q.mass
  exchange := Q.exchange
  openHalfMeasureFinite := Q.openHalfMeasureFinite
  gramFeature_aestronglyMeasurable := Q.gramFeature_aestronglyMeasurable
  gramFeatureBound := Q.gramFeatureBound
  gramFeature_norm_le := Q.gramFeature_norm_le
  boundaryMoment_aestronglyMeasurable :=
    Q.boundaryMoment_aestronglyMeasurable
  boundaryMoment_sq_integrable := Q.boundaryMoment_sq_integrable
  boundaryTransfer := Q.boundaryTransfer
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_defect_bound :=
    Q.boundaryTransfer_exponential_defect_bound

/-- The exponential Poincaré package generates the direct boundary-`L²`
Poincaré certificate. -/
noncomputable def toApproximatingBoundaryL2PoincareGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate
    |>.toApproximatingBoundaryL2PoincareGapCertificate

/-- The exponential Poincaré package generates the completed finite Wilson OS
vacuum-sector decay certificate with mass `Q.mass`. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingMeasurableBoundaryL2PoincareGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2PoincareGapCertificate

end MathlibAnalytic
end MGAP4D

end
