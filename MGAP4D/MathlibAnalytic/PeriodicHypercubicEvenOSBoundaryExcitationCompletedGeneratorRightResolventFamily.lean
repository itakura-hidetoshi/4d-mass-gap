import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventCore
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The inverse of `lambda I - G` has derivative `-R²` at every unit shift. -/
theorem ringInverse_smul_one_sub_hasDerivAt
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda : ℝ)
    (hunit : IsUnit (lambda • (1 : R) - G)) :
    HasDerivAt
      (fun mu : ℝ => Ring.inverse (mu • (1 : R) - G))
      (-(Ring.inverse (lambda • (1 : R) - G) *
        Ring.inverse (lambda • (1 : R) - G)))
      lambda := by
  have hshift :
      HasDerivAt (fun mu : ℝ => mu • (1 : R) - G) (1 : R) lambda := by
    simpa using ((hasDerivAt_id lambda).smul_const (1 : R)).sub_const G
  have hcomp :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit).comp_hasDerivAt lambda hshift
  have hinverse :
      Ring.inverse (lambda • (1 : R) - G) = ↑(hunit.unit⁻¹) := by
    simpa only [hunit.unit_spec] using Ring.inverse_unit hunit.unit
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinverse] using hcomp

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedGeneratorRightResolventFamilyPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Proof-independent total right-resolvent family. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
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
    (lambda •
        (1 :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →L[ℝ]
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta) -
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)

/-- Above one, the proof-independent right ring inverse equals the positive Green resolvent. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda := by
  have hunit :
      IsUnit
        (lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta) := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
        H N hN beta hbeta lambda hlambda
  have hright :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda = 1 := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily] using
      mul_ringInverse_eq_one_of_isUnit
        (lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta)
        hunit
  exact
    (left_inv_eq_right_inv
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreen_mul_generator
        H N hN beta hbeta lambda hlambda)
      hright).symm

/-- The total right-resolvent family is differentiable on `(1,∞)` with derivative `-S²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    HasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      (-(periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda))
      lambda := by
  have hunit :
      IsUnit
        (lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta) := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
        H N hN beta hbeta lambda hlambda
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily] using
    ringInverse_smul_one_sub_hasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda hunit

/-- Fixed-vector right-resolvent quadratic matrix elements inherit derivative `-⟪S²u,u⟫`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    HasDerivAt
      (fun mu : ℝ =>
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta mu u)
          u)
      (- inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) u)
        u)
      lambda := by
  have hquad :=
    HasDerivAt.quadraticEvaluation
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
        H N hN beta hbeta lambda hlambda)
      u
  simpa only [ContinuousLinearMap.neg_apply, inner_neg_left] using hquad

/-- Every fixed-vector right-resolvent quadratic derivative value is nonpositive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_derivative_nonpos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    - inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) u)
        u ≤ 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
    H N hN beta hbeta lambda hlambda]
  have hpow :
      0 ≤ inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda) ^ 2) u) u :=
    realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_isSelfAdjoint
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
        H N hN beta hbeta lambda hlambda)
      2 u
  simpa [pow_two] using neg_nonpos.mpr hpow

/-- Audit-visible package for the completed positive right-resolvent calculus. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  generatorUpperQuadraticBound :
    ∀ u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta u)
          u ≤ ‖u‖ ^ 2
  aboveOneResolvent :
    ∀ lambda, 1 < lambda →
      lambda ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta)
  rightResolventPositive :
    ∀ lambda, ∀ hlambda : 1 < lambda, ∀ u,
      0 ≤ inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda u)
        u
  rightResolventNormBound :
    ∀ lambda, ∀ hlambda : 1 < lambda,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda‖ ≤ (lambda - 1)⁻¹
  rightResolventDerivative :
    ∀ lambda, 1 < lambda →
      HasDerivAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta)
        (-(periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda *
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda))
        lambda

/-- Construct the completed positive right-resolvent package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventPackage
      H N hN beta hbeta :=
  { generatorUpperQuadraticBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_le_norm_sq
        H N hN beta hbeta
    aboveOneResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_lt
        H N hN beta hbeta
    rightResolventPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
        H N hN beta hbeta
    rightResolventNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta
    rightResolventDerivative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
