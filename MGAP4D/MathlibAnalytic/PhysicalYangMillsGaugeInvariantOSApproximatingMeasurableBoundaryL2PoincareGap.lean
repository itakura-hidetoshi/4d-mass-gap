import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingMeasurableBoundaryL2QuadraticGap
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance measurableBoundaryL2PoincareSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- A finite Wilson shared-boundary Poincaré-gap package with all routine
integrability and `L²` membership generated from primitive measurable data.

The model-specific quantitative input is the defect inequality

`defect(t) * ‖v‖² ≤ ‖v‖² - ‖K_{n,t} v‖²`.

Open-half Gram integrability follows from finite measure, AE strong
measurability, and a uniform norm bound.  Boundary-moment `MemLp` follows from
AE strong measurability and squared-norm integrability.  The existing Poincaré
constructor then generates quadratic contraction, operator-norm contraction,
finite Wilson OS decay, and the continuum Hamiltonian gap route. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
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
  defectFactor : NNReal → ℝ
  defectFactor_nonneg : ∀ t, 0 ≤ defectFactor t
  defectFactor_le_one : ∀ t, defectFactor t ≤ 1
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (1 - defectFactor (t + t))))
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
  boundaryTransfer_defect_bound :
    ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
        (halfExtent n) N),
      defectFactor t * ‖v‖ ^ 2 ≤
        ‖v‖ ^ 2 - ‖boundaryTransfer n t v‖ ^ 2

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate

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

/-- Generate boundary-moment `L²` membership from measurability and squared-norm
integrability. -/
theorem boundaryMoment_memLp
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
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

/-- Generate the direct boundary-`L²` Poincaré certificate. -/
noncomputable def toApproximatingBoundaryL2PoincareGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  defectFactor := Q.defectFactor
  defectFactor_nonneg := Q.defectFactor_nonneg
  defectFactor_le_one := Q.defectFactor_le_one
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
  boundaryTransfer := Q.boundaryTransfer
  boundaryMoment_intertwining := by
    intro n t
    dsimp only
    intro F
    simpa only [boundaryMoment_memLp] using
      Q.boundaryMoment_intertwining n t F
  boundaryTransfer_defect_bound := Q.boundaryTransfer_defect_bound

/-- The measurable Poincaré package generates the boundary-`L²` quadratic gap
certificate. -/
noncomputable def toApproximatingBoundaryL2QuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingBoundaryL2QuadraticGapCertificate

/-- The measurable Poincaré package generates the integrated boundary-moment
gap certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- The measurable Poincaré package generates the completed finite Wilson OS
vacuum-sector norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingMeasurableBoundaryL2PoincareGapCertificate

end MathlibAnalytic
end MGAP4D

end