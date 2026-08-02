import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableIntegralTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

local instance boundaryVacuumMomentNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryVacuumMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryVacuumMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryVacuumMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryVacuumMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryVacuumMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The boundary Gram moment of the constant positive-half observable.

This is the finite Wilson OS vacuum wavefunction on the reflection-fixed
boundary. Its square is the boundary marginal density of the Gibbs law. -/
noncomputable def periodicHypercubicEvenBoundaryVacuumMoment
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)

/-- The completed positive Gram feature for the vacuum is jointly measurable
in the shared boundary and positive open-half coordinates. -/
theorem periodicHypercubicEvenBoundaryVacuumGramFeature_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hdiag : Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (z.1, (z.2,
          periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))) :=
    measurable_fst.prodMk
      (measurable_snd.prodMk (hc.comp measurable_snd))
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hsqrt : Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (z.1, (z.2,
              periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))).toReal)) :=
    Real.continuous_sqrt.measurable.comp
      ((ENNReal.measurable_toReal.comp hd).comp hdiag)
  have heq :
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) =
      fun z =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (z.1, (z.2,
              periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))).toReal) := by
    funext z
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity
        H N hN beta hbeta z.1 z.2
  rw [heq]
  exact hsqrt

/-- For every fixed boundary configuration, the vacuum Gram feature is
integrable over the positive open half. -/
theorem periodicHypercubicEvenBoundaryVacuumGramFeature_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Integrable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let one : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ := 1
  have h :=
    periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
      H N hN beta hbeta one b
  have heq :
      periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta one b =
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b := by
    funext x
    simp [one, periodicHypercubicEvenBoundaryObservableGramFeature]
  rwa [heq] at h

/-- The Wilson boundary vacuum moment is measurable. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  exact
    (periodicHypercubicEvenBoundaryVacuumGramFeature_measurable
      H N hN beta hbeta).stronglyMeasurable.integral_prod_right'.measurable

/-- The Wilson boundary vacuum moment is nonnegative. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    0 ≤ periodicHypercubicEvenBoundaryVacuumMoment
      H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  exact integral_nonneg fun x =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
      H N hN beta hbeta b x

/-- Integrating the boundary-fibered Gibbs density over both open halves gives
exactly the square of the boundary vacuum moment. -/
theorem periodicHypercubicEvenBoundaryFiberedGibbsDensity_integral_eq_vacuumMoment_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    (∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta b ^ 2 := by
  have htransport :
      (∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x,
            periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simpa using
      (periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
        H N hN beta hbeta (fun _ => (1 : ℝ)) b x)
  have hone :
      Integrable
        (periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta (fun _ => (1 : ℝ)) b)
        (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    have h :=
      periodicHypercubicEvenBoundaryVacuumGramFeature_integrable
        H N hN beta hbeta b
    have heq :
        periodicHypercubicEvenBoundaryObservableGramFeature
            H N hN beta hbeta (fun _ => (1 : ℝ)) b =
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b := by
      funext x
      simp [periodicHypercubicEvenBoundaryObservableGramFeature]
    rwa [heq]
  have hgram :=
    periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_eq_norm_sq
      H N hN beta hbeta (fun _ => (1 : ℝ)) b hone
  rw [← htransport]
  simpa [periodicHypercubicEvenBoundaryVacuumMoment,
    periodicHypercubicEvenBoundaryObservableGramFeature,
    Real.norm_eq_abs,
    abs_of_nonneg
      (periodicHypercubicEvenBoundaryVacuumMoment_nonneg
        H N hN beta hbeta b)] using hgram

end

end MathlibAnalytic
end MGAP4D
