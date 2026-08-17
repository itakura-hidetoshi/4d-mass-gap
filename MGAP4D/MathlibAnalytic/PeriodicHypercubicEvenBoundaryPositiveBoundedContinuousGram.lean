import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity

/-!
# Boundary-dependent positive-half Wilson Gram positivity

The finite Wilson reflection-positive theorem was previously packaged for a
bounded continuous observable depending only on the positive open half.  A
rational positive-time cylinder naturally also sees the reflection-fixed
boundary at time zero.  The correct finite domain is therefore

`BoundaryConfiguration × OpenHalfConfiguration`.

This file extends the existing Gram argument to that natural domain.  No new
reflection-positivity premise is introduced: for each fixed boundary `b`, the
observable is sliced to an ordinary bounded continuous open-half observable and
the already proved Wilson Gram theorem is applied fiberwise.  Integrating the
resulting nonnegative fibers over the shared boundary preserves positivity.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundaryPositiveGramNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPositiveGramTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPositiveGramCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryPositiveGramSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryPositiveGramMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryPositiveGramBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The natural finite positive-time carrier: reflection-fixed boundary data
together with the positive open half. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration
    (H N : ℕ) :=
  PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N

/-- Fixing the shared boundary turns a bounded continuous boundary-positive
observable into the ordinary bounded continuous open-half observable consumed
by the existing finite Wilson Gram theorem. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveObservableSlice
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ :=
  f.compContinuous
    ⟨(fun x => (b, x)), continuous_const.prodMk continuous_id⟩

@[simp]
theorem periodicHypercubicEvenBoundaryPositiveObservableSlice_apply
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryPositiveObservableSlice H N f b x = f (b, x) :=
  rfl

/-- For one fixed shared boundary, the orientation-corrected Wilson quadratic
integral of a bounded continuous boundary-positive observable is nonnegative.

The proof is exactly the existing scalar Gram-square theorem applied to the
boundary slice. -/
theorem periodicHypercubicEvenBoundaryPositiveObservable_original_iteratedIntegral_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    0 ≤ ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f (b, x) *
          f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let fb := periodicHypercubicEvenBoundaryPositiveObservableSlice H N f b
  have hfb : Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta fb b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
    periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
      H N hN beta hbeta fb b
  have hcorrected :=
    periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_nonneg
      H N hN beta hbeta fb b hfb
  have htransport :
      (∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
          (fb x * fb y)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal *
          (fb x * fb (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
      H N hN beta hbeta fb b x
  have hslice :
      0 ≤ ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal *
          (fb x * fb (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    rw [← htransport]
    exact hcorrected
  simpa [fb, periodicHypercubicEvenBoundaryPositiveObservableSlice] using hslice

/-- Boundary-dependent finite Wilson Gram positivity.

A bounded continuous observable may depend simultaneously on the shared
reflection-fixed boundary and the positive open half.  The boundary-conditioned
quadratic form is nonnegative for every boundary, hence its boundary Haar
average is nonnegative.  This is the finite theorem needed to admit rational
positive-time cylinders containing time zero. -/
theorem periodicHypercubicEvenBoundaryPositiveObservable_boundaryIntegral_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ) :
    0 ≤ ∫ b, ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f (b, x) *
          f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  exact integral_nonneg fun b =>
    periodicHypercubicEvenBoundaryPositiveObservable_original_iteratedIntegral_nonneg
      H N hN beta hbeta f b

end

end MathlibAnalytic
end MGAP4D
