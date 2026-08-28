import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventFamily
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventCompleteMonotonicityGeneric
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedRightCompleteMonotonicitySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedRightCompleteMonotonicityPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed right-resolvent family is analytic at every parameter above
its sharp upper spectral endpoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_analyticAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    AnalyticAt ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
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
    ringInverse_smul_one_sub_analyticAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda hunit

/-- Analyticity holds on the full open above-one half-line. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_analyticOnNhd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      (Set.Ioi 1) := by
  intro lambda hlambda
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_analyticAt
      H N hN beta hbeta lambda hlambda

/-- The concrete completed right resolvent satisfies the sole differential
hypothesis required by the generic all-order complete-monotonicity theorem.
Keeping this bridge at first order avoids forcing Lean to normalize a giant
dependent `iteratedDeriv` expression on the concrete carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivWithinAt_neg_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    HasDerivWithinAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      (-((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda) ^ 2))
      (Set.Ioi 1) lambda := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
      H N hN beta hbeta lambda hlambda
  have h' :
      HasDerivAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta)
        (-((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta lambda) ^ 2))
        lambda := by
    simpa only [pow_two] using h
  exact h'.hasDerivWithinAt

/-- Above one, the proof-independent right resolvent is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
    H N hN beta hbeta lambda hlambda]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_isSelfAdjoint
      H N hN beta hbeta lambda hlambda

/-- Above one, the proof-independent right resolvent has nonnegative quadratic
form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda u)
      u := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
    H N hN beta hbeta lambda hlambda]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
      H N hN beta hbeta lambda hlambda u

/-- Every power of the positive self-adjoint completed right resolvent has
nonnegative quadratic form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_pow_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (n : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda) ^ n) u)
      u := by
  exact
    realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_isSelfAdjoint
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_inner_nonneg
        H N hN beta hbeta lambda hlambda)
      n u

/-- The positive factor appearing after sign correction of the exact abstract
`n`-th scalar derivative is nonnegative on the completed carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFactorialPower_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    0 ≤ (n.factorial : ℝ) *
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta lambda) ^ (n + 1)) u)
        u := by
  exact
    realContinuousLinearMap_factorial_mul_pow_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_isSelfAdjoint
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_inner_nonneg
        H N hN beta hbeta lambda hlambda)
      n u

/-- The exact sign-weighted factorial operator value obeys the sharp distance
to the spectral endpoint estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingFactorialPower_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    ‖((-1 : ℝ) ^ n) •
        ((n.factorial : ℝ) •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) ^ (n + 1))‖ ≤
      (n.factorial : ℝ) * ((lambda - 1)⁻¹) ^ (n + 1) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
      H N hN beta hbeta lambda
  have hnorm : ‖S‖ ≤ (lambda - 1)⁻¹ := by
    dsimp [S]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
      H N hN beta hbeta lambda hlambda]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta lambda hlambda
  change
    ‖((-1 : ℝ) ^ n) • ((n.factorial : ℝ) • S ^ (n + 1))‖ ≤
      (n.factorial : ℝ) * ((lambda - 1)⁻¹) ^ (n + 1)
  exact
    continuousLinearMap_alternating_factorial_smul_pow_norm_le
      S n ((lambda - 1)⁻¹) hnorm

/-- After multiplying the exact abstract derivative value by its alternating
sign, the two signs cancel and the remaining completed quadratic factor is
nonnegative.  Together with
`rightResolvent_quadratic_iteratedDeriv_eq_alternating_factorial` and the
concrete first-order bridge above, this is the completed complete-monotonicity
receipt without re-normalizing `iteratedDeriv` on the dependent carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingFactorialQuadratic_signCorrected_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    0 ≤ ((-1 : ℝ) ^ n) *
      (((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) *
          inner ℝ
            (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda) ^ (n + 1)) u)
            u)) := by
  have hb :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFactorialPower_inner_nonneg
      H N hN beta hbeta u n lambda hlambda
  have hs : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    calc
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n + n) :=
        (pow_add (-1 : ℝ) n n).symm
      _ = (-1 : ℝ) ^ (2 * n) := by congr 1 <;> omega
      _ = ((-1 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = 1 := by norm_num
  calc
    0 ≤ (n.factorial : ℝ) *
        inner ℝ
          (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) ^ (n + 1)) u)
          u := hb
    _ = ((-1 : ℝ) ^ n) *
        (((-1 : ℝ) ^ n) *
          ((n.factorial : ℝ) *
            inner ℝ
              (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
                H N hN beta hbeta lambda) ^ (n + 1)) u)
              u)) := by
      rw [← mul_assoc, hs, one_mul]

/-- Audit-visible completed above-one complete-monotonicity package.  The exact
all-order `iteratedDeriv` identity lives once in the generic layer; this
concrete package supplies precisely its derivative hypothesis and the positive
factor needed after alternating-sign cancellation. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventCompleteMonotonicityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  analyticOnNhd :
    AnalyticOnNhd ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      (Set.Ioi 1)
  derivativeHypothesis :
    ∀ (lambda : ℝ), 1 < lambda →
      HasDerivWithinAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta)
        (-((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta lambda) ^ 2))
        (Set.Ioi 1) lambda
  factorialDistanceBound :
    ∀ (n : ℕ) (lambda : ℝ), 1 < lambda →
      ‖((-1 : ℝ) ^ n) •
          ((n.factorial : ℝ) •
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda) ^ (n + 1))‖ ≤
        (n.factorial : ℝ) * ((lambda - 1)⁻¹) ^ (n + 1)
  factorialPowerQuadraticNonnegative :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) (n : ℕ) (lambda : ℝ), 1 < lambda →
      0 ≤ (n.factorial : ℝ) *
        inner ℝ
          (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) ^ (n + 1)) u)
          u

/-- Construct the completed above-one complete-monotonicity package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventCompleteMonotonicityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventCompleteMonotonicityPackage
      H N hN beta hbeta :=
  { analyticOnNhd :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_analyticOnNhd
        H N hN beta hbeta
    derivativeHypothesis :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivWithinAt_neg_sq
        H N hN beta hbeta
    factorialDistanceBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingFactorialPower_norm_le
        H N hN beta hbeta
    factorialPowerQuadraticNonnegative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFactorialPower_inner_nonneg
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
