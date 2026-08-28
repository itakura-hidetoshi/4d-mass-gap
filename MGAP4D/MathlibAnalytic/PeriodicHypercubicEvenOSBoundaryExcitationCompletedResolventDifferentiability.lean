import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventIdentity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- In a real normed Banach algebra, the inverse of the affine shift
`G - lambda • 1` has derivative equal to the square of the inverse whenever
the shift is a unit.  This is the abstract resolvent derivative identity. -/
theorem ringInverse_sub_smul_one_hasDerivAt
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda : ℝ)
    (hunit : IsUnit (G - lambda • (1 : R))) :
    HasDerivAt
      (fun mu : ℝ => Ring.inverse (G - mu • (1 : R)))
      (Ring.inverse (G - lambda • (1 : R)) *
        Ring.inverse (G - lambda • (1 : R)))
      lambda := by
  have hshift :
      HasDerivAt (fun mu : ℝ => G - mu • (1 : R)) (-(1 : R)) lambda := by
    simpa using ((hasDerivAt_id lambda).smul_const (1 : R)).const_sub G
  have hcomp :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit).comp_hasDerivAt lambda hshift
  have hinverse :
      Ring.inverse (G - lambda • (1 : R)) = ↑(hunit.unit⁻¹) := by
    simpa only [hunit.unit_spec] using Ring.inverse_unit hunit.unit
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinverse] using hcomp

/-- Ring inversion of a unit is its inverse unit. -/
theorem ringInverse_eq_unit_inv
    {R : Type*}
    [Ring R]
    (x : R)
    (hx : IsUnit x) :
    Ring.inverse x = ↑(hx.unit⁻¹) := by
  simpa only [hx.unit_spec] using Ring.inverse_unit hx.unit

/-- A unit multiplied by its ring inverse is one. -/
theorem mul_ringInverse_eq_one_of_isUnit
    {R : Type*}
    [Ring R]
    (x : R)
    (hx : IsUnit x) :
    x * Ring.inverse x = 1 := by
  rw [ringInverse_eq_unit_inv x hx]
  simpa only [hx.unit_spec] using hx.unit.mul_inv

/-- If an element is norm-bounded by a nonnegative number, its square is
bounded by the square of that number. -/
theorem norm_mul_self_le_sq
    {R : Type*}
    [SeminormedRing R]
    (x : R)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hx : ‖x‖ ≤ M) :
    ‖x * x‖ ≤ M ^ 2 := by
  calc
    ‖x * x‖ ≤ ‖x‖ * ‖x‖ := norm_mul_le x x
    _ ≤ M * M := mul_le_mul hx hx (norm_nonneg x) hM
    _ = M ^ 2 := by ring

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedResolventDifferentiabilitySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedResolventDifferentiabilityPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A proof-independent total real resolvent family for the completed
one-step generator.  Below the explicit finite-volume gap it agrees with the
positive shifted Green operator already constructed. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  Ring.inverse
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta -
      lambda •
        (1 :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →L[ℝ]
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta))

/-- Below the finite-volume gap, the proof-independent ring inverse equals the
previously constructed positive shifted Green operator.  The proof uses
uniqueness of a left/right inverse and never unfolds the proof-dependent unit. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda := by
  have hunit :
      IsUnit
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta -
          lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta)) := by
    simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
        H N hN beta hbeta lambda hlambda
  have hright :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda = 1 := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily] using
      mul_ringInverse_eq_one_of_isUnit
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta -
          lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta))
        hunit
  exact
    (left_inv_eq_right_inv
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreen_mul_generator
        H N hN beta hbeta lambda hlambda)
      hright).symm

/-- The completed below-gap resolvent family is operator-norm differentiable.
Its exact derivative value is the square of the resolvent itself. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    HasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda)
      lambda := by
  have hunit :
      IsUnit
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta -
          lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta)) := by
    simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
        H N hN beta hbeta lambda hlambda
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily] using
    ringInverse_sub_smul_one_hasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda hunit

/-- The exact derivative value furnished by `HasDerivAt` obeys the explicit
finite-volume inverse-gap square bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_derivativeValue_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹ ^ 2 := by
  have hgreen :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹ ^ 2 :=
    norm_mul_self_le_sq
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹)
      (inv_nonneg.mpr
        (sub_nonneg.mpr hlambda.le))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta lambda hlambda)
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
      H N hN beta hbeta lambda hlambda] using hgreen

/-- Audit-visible package for the completed finite-volume below-gap resolvent
calculus.  `HasDerivAt` is retained as the primary operator-norm
Fréchet-differentiability receipt, avoiding any proof-irrelevant rewrapping of
the huge dependent carrier. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventDifferentiabilityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  agreesWithGreen :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda
  hasDerivativeSquare :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      HasDerivAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda)
        lambda
  derivativeValueNormBound :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹ ^ 2

/-- Construct the completed finite-volume below-gap resolvent-calculus
package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedResolventDifferentiabilityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventDifferentiabilityPackage
      H N hN beta hbeta :=
  { agreesWithGreen :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
        H N hN beta hbeta
    hasDerivativeSquare :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasDerivAt
        H N hN beta hbeta
    derivativeValueNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_derivativeValue_norm_le
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
