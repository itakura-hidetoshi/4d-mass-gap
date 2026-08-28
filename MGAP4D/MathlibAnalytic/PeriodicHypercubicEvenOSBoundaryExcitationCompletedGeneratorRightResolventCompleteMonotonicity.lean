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

/-- The sign-weighted factorial operator family representing the all-order
right-resolvent derivative hierarchy. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ℝ →
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta) :=
  ((-1 : ℝ) ^ n) •
    (fun lambda =>
      (n.factorial : ℝ) •
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta lambda) ^ (n + 1))

/-- Consecutive members of the completed alternating derivative hierarchy are
linked by exact differentiation on `(1,∞)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily_hasDerivWithinAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    HasDerivWithinAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
        H N hN beta hbeta (n + 1) lambda)
      (Set.Ioi 1) lambda := by
  have hres :
      ∀ {mu : ℝ}, 1 < mu →
        HasDerivWithinAt
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta)
          (-((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta mu) ^ 2))
          (Set.Ioi 1) mu := by
    intro mu hmu
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
        H N hN beta hbeta mu hmu
    have h' :
        HasDerivAt
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta)
          (-((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta mu) ^ 2)) mu := by
      simpa only [pow_two] using h
    exact h'.hasDerivWithinAt
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
  exact
    rightResolvent_alternatingFactorialDerivativeStep_hasDerivWithinAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      1 hres n hlambda

/-- Fixed-vector evaluation of the operator derivative hierarchy. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (n : ℕ) : ℝ → ℝ :=
  fun lambda =>
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
        H N hN beta hbeta n lambda u)
      u

/-- The scalar derivative candidates obey the same all-order recurrence on the
completed carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily_hasDerivWithinAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    HasDerivWithinAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
        H N hN beta hbeta u n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
        H N hN beta hbeta u (n + 1) lambda)
      (Set.Ioi 1) lambda := by
  have hop :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily_hasDerivWithinAt
      H N hN beta hbeta n lambda hlambda
  have hquad := HasDerivWithinAt.quadraticEvaluation hop u
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily] using hquad

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

/-- The all-order operator candidate obeys the sharp factorial distance bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
        H N hN beta hbeta n lambda‖ ≤
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
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
  change
    ‖((-1 : ℝ) ^ n) • ((n.factorial : ℝ) • S ^ (n + 1))‖ ≤
      (n.factorial : ℝ) * ((lambda - 1)⁻¹) ^ (n + 1)
  exact
    continuousLinearMap_alternating_factorial_smul_pow_norm_le
      S n ((lambda - 1)⁻¹) hnorm

/-- The sign correction of every fixed-vector formal derivative value is
nonnegative. The generic layer identifies these values with the exact abstract
iterated derivatives. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily_signCorrected_nonneg
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
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
        H N hN beta hbeta u n lambda := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, smul_eq_mul]
  let s : ℝ := (-1 : ℝ) ^ n
  let b : ℝ :=
    (n.factorial : ℝ) *
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta lambda ^ (n + 1)) u)
        u
  have hs : s * s = 1 := by
    dsimp [s]
    calc
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n + n) :=
        (pow_add (-1 : ℝ) n n).symm
      _ = (-1 : ℝ) ^ (2 * n) := by congr 1 <;> omega
      _ = ((-1 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = 1 := by norm_num
  have hb : 0 ≤ b := by
    dsimp [b]
    exact
      realContinuousLinearMap_factorial_mul_pow_inner_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta lambda)
        (by
          rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
            H N hN beta hbeta lambda hlambda]
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_isSelfAdjoint
              H N hN beta hbeta lambda hlambda)
        (by
          intro v
          rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
            H N hN beta hbeta lambda hlambda]
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
              H N hN beta hbeta lambda hlambda v)
        n u
  change 0 ≤ s * (s * b)
  calc
    0 ≤ b := hb
    _ = s * (s * b) := by rw [← mul_assoc, hs, one_mul]

/-- Audit-visible completed above-one complete-monotonicity package. -/
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
  operatorDerivativeRecurrence :
    ∀ (n : ℕ) (lambda : ℝ), 1 < lambda →
      HasDerivWithinAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
          H N hN beta hbeta n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
          H N hN beta hbeta (n + 1) lambda)
        (Set.Ioi 1) lambda
  scalarDerivativeRecurrence :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) (n : ℕ) (lambda : ℝ), 1 < lambda →
      HasDerivWithinAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
          H N hN beta hbeta u n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
          H N hN beta hbeta u (n + 1) lambda)
        (Set.Ioi 1) lambda
  factorialDistanceBound :
    ∀ (n : ℕ) (lambda : ℝ), 1 < lambda →
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily
          H N hN beta hbeta n lambda‖ ≤
        (n.factorial : ℝ) * ((lambda - 1)⁻¹) ^ (n + 1)
  signCorrectedNonnegative :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) (n : ℕ) (lambda : ℝ), 1 < lambda →
      0 ≤ ((-1 : ℝ) ^ n) *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily
          H N hN beta hbeta u n lambda

/-- Construct the full completed right-resolvent hierarchy package. -/
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
    operatorDerivativeRecurrence :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily_hasDerivWithinAt
        H N hN beta hbeta
    scalarDerivativeRecurrence :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily_hasDerivWithinAt
        H N hN beta hbeta
    factorialDistanceBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventAlternatingDerivativeFamily_norm_le
        H N hN beta hbeta
    signCorrectedNonnegative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadraticDerivativeFamily_signCorrected_nonneg
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
