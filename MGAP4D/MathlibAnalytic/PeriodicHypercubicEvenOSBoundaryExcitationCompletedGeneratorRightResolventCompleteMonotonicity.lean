import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventFamily
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchy
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The right affine inverse is real analytic at every unit shift. -/
theorem ringInverse_smul_one_sub_analyticAt
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda : ℝ)
    (hunit : IsUnit (lambda • (1 : R) - G)) :
    AnalyticAt ℝ
      (fun mu : ℝ => Ring.inverse (mu • (1 : R) - G))
      lambda := by
  have hid : AnalyticAt ℝ (fun mu : ℝ => mu) lambda := analyticAt_id
  have hone : AnalyticAt ℝ (fun _ : ℝ => (1 : R)) lambda := analyticAt_const
  have hG : AnalyticAt ℝ (fun _ : ℝ => G) lambda := analyticAt_const
  have hsmul : AnalyticAt ℝ (fun mu : ℝ => mu • (1 : R)) lambda :=
    hid.smul hone
  have hshift :
      AnalyticAt ℝ (fun mu : ℝ => mu • (1 : R) - G) lambda :=
    hsmul.sub hG
  have hinverse :
      AnalyticAt ℝ Ring.inverse (lambda • (1 : R) - G) := by
    simpa only [hunit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℝ) hunit.unit)
  exact AnalyticAt.comp'
    (𝕜 := ℝ)
    (g := fun x : R => Ring.inverse x)
    (f := fun mu : ℝ => mu • (1 : R) - G)
    hinverse hshift

/-- If `S' = -S²` on a right half-line, then `(S^k)' = -k S^(k+1)` there. -/
theorem rightResolvent_pow_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (k : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda) :
    HasDerivWithinAt
      (fun mu => res mu ^ k)
      (-((k : ℝ) • res lambda ^ (k + 1)))
      (Set.Ioi edge)
      lambda := by
  induction k with
  | zero =>
      simpa using
        (hasDerivWithinAt_const lambda (Set.Ioi edge) (1 : A))
  | succ k ih =>
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ)
        (𝔸 := A)
        ih (hres hlambda)
      have hmul' :
          HasDerivWithinAt
            (fun mu => res mu ^ (k + 1))
            ((-((k : ℝ) • res lambda ^ (k + 1))) * res lambda +
              res lambda ^ k * (-(res lambda ^ 2)))
            (Set.Ioi edge)
            lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((-((k : ℝ) • res lambda ^ (k + 1))) * res lambda +
              res lambda ^ k * (-(res lambda ^ 2))) =
            -(((Nat.succ k : ℕ) : ℝ) •
              res lambda ^ (Nat.succ k + 1)) := by
        let x := res lambda
        change
          (-((k : ℝ) • x ^ (k + 1))) * x +
              x ^ k * (-(x ^ 2)) =
            -(((Nat.succ k : ℕ) : ℝ) • x ^ (Nat.succ k + 1))
        have hfirst :
            ((k : ℝ) • x ^ (k + 1)) * x =
              (k : ℝ) • x ^ (k + 2) := by
          rw [Algebra.smul_mul_assoc]
          congr 1
          simpa [Nat.add_assoc] using (pow_succ x (k + 1)).symm
        have hsecond : x ^ k * x ^ 2 = x ^ (k + 2) := by
          simpa using (pow_add x k 2).symm
        rw [neg_mul, hfirst, mul_neg, hsecond,
          show Nat.succ k + 1 = k + 2 by omega, Nat.cast_succ]
        module
      rw [hderiv] at hmul'
      exact hmul'

/-- Factorial powers on a right resolvent acquire one minus sign at each
successive derivative step. -/
theorem rightResolvent_factorialDerivativeStep_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda) :
    HasDerivWithinAt
      (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
      (-(((n + 1).factorial : ℝ) • res lambda ^ (n + 2)))
      (Set.Ioi edge)
      lambda := by
  have hpow :=
    rightResolvent_pow_hasDerivWithinAt res edge hres (n + 1) hlambda
  have hscaled :
      HasDerivWithinAt
        (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
        ((n.factorial : ℝ) •
          (-(((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2))))
        (Set.Ioi edge) lambda := by
    simpa only [Pi.smul_apply] using
      (HasDerivWithinAt.const_smul
        (𝕜 := ℝ) (R := ℝ) (F := A)
        (n.factorial : ℝ) hpow)
  simpa [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    smul_smul, mul_comm, Nat.add_assoc] using hscaled

/-- The sign-weighted factorial power has the next sign-weighted factorial
power as its derivative. -/
theorem rightResolvent_alternatingFactorialDerivativeStep_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda) :
    HasDerivWithinAt
      (fun mu =>
        ((-1 : ℝ) ^ n) •
          ((n.factorial : ℝ) • res mu ^ (n + 1)))
      (((-1 : ℝ) ^ (n + 1)) •
        (((n + 1).factorial : ℝ) • res lambda ^ (n + 2)))
      (Set.Ioi edge)
      lambda := by
  have hbase :=
    rightResolvent_factorialDerivativeStep_hasDerivWithinAt
      res edge hres n hlambda
  have hsigned :=
    HasDerivWithinAt.const_smul
      (𝕜 := ℝ) (R := ℝ) (F := A)
      ((-1 : ℝ) ^ n) hbase
  simpa [pow_succ, smul_smul] using hsigned

/-- Exact scalar all-order formula for a fixed-vector right-resolvent matrix
element on an abstract open half-line. -/
theorem rightResolvent_quadratic_iteratedDerivWithin_eq_alternating_factorial
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda)
    (u : E) :
    iteratedDerivWithin n
        (fun mu : ℝ => inner ℝ (res mu u) u)
        (Set.Ioi edge) lambda =
      ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) *
          inner ℝ ((res lambda ^ (n + 1)) u) u) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (fun mu : ℝ => inner ℝ (res mu u) u)
                (Set.Ioi edge))
              (Set.Ioi edge) lambda =
            derivWithin
              (fun mu : ℝ =>
                ((-1 : ℝ) ^ n) *
                  ((n.factorial : ℝ) *
                    inner ℝ ((res mu ^ (n + 1)) u) u))
              (Set.Ioi edge) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hop :=
        rightResolvent_alternatingFactorialDerivativeStep_hasDerivWithinAt
          res edge hres n hlambda
      have hquad := HasDerivWithinAt.quadraticEvaluation hop u
      have hstep :
          HasDerivWithinAt
            (fun mu : ℝ =>
              ((-1 : ℝ) ^ n) *
                ((n.factorial : ℝ) *
                  inner ℝ ((res mu ^ (n + 1)) u) u))
            (((-1 : ℝ) ^ (n + 1)) *
              (((n + 1).factorial : ℝ) *
                inner ℝ ((res lambda ^ (n + 2)) u) u))
            (Set.Ioi edge) lambda := by
        simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
          mul_assoc] using hquad
      exact hstep.derivWithin (isOpen_Ioi.uniqueDiffOn lambda hlambda)

/-- Ordinary scalar all-order formula at interior points of the right
resolvent half-line. -/
theorem rightResolvent_quadratic_iteratedDeriv_eq_alternating_factorial
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (edge : ℝ)
    (hres :
      ∀ {lambda : ℝ}, edge < lambda →
        HasDerivWithinAt res (-(res lambda ^ 2)) (Set.Ioi edge) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : edge < lambda)
    (u : E) :
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
      ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) *
          inner ℝ ((res lambda ^ (n + 1)) u) u) := by
  calc
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
        iteratedDerivWithin n
          (fun mu : ℝ => inner ℝ (res mu u) u)
          (Set.Ioi edge) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := fun mu : ℝ => inner ℝ (res mu u) u)
        isOpen_Ioi hlambda).symm
    _ = ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) *
          inner ℝ ((res lambda ^ (n + 1)) u) u) :=
      rightResolvent_quadratic_iteratedDerivWithin_eq_alternating_factorial
        res edge hres n hlambda u

/-- Multiplying a factorial power by the alternating sign does not change its
operator-norm estimate. -/
theorem continuousLinearMap_alternating_factorial_smul_pow_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (n : ℕ)
    (M : ℝ)
    (hA : ‖A‖ ≤ M) :
    ‖((-1 : ℝ) ^ n) • ((n.factorial : ℝ) • A ^ (n + 1))‖ ≤
      (n.factorial : ℝ) * M ^ (n + 1) := by
  rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact continuousLinearMap_factorial_smul_pow_norm_le A n M hA

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

/-- The completed right-resolvent family is analytic at every `lambda > 1`. -/
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

/-- The completed right-resolvent family is analytic on the whole open
half-line above the sharp upper spectral endpoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_analyticOnNhd :
    ∀ (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta),
    AnalyticOnNhd ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      (Set.Ioi 1) := by
  intro H N hN beta hbeta lambda hlambda
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_analyticAt
      H N hN beta hbeta lambda hlambda

/-- Above one, the total right resolvent is self-adjoint. -/
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

/-- Above one, the total right resolvent has nonnegative quadratic form. -/
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

/-- Every power of the positive right resolvent has nonnegative fixed-vector
quadratic form. -/
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
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda ^ n) u)
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

/-- Exact all-order scalar derivative formula for the completed right
resolvent. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_iteratedDeriv_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    iteratedDeriv n
        (fun mu : ℝ =>
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta mu u)
            u)
        lambda =
      ((-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) *
          inner ℝ
            ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda ^ (n + 1)) u)
            u) := by
  apply rightResolvent_quadratic_iteratedDeriv_eq_alternating_factorial
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
      H N hN beta hbeta)
    1
  · intro mu hmu
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
  · exact hlambda
  · exact u

/-- The exact all-order operator candidate has the sharp factorial distance
bound above the upper spectral endpoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_alternatingFactorialDerivativeValue_norm_le
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
  exact
    continuousLinearMap_alternating_factorial_smul_pow_norm_le
      S n ((lambda - 1)⁻¹) hnorm

/-- Every fixed-vector right-resolvent amplitude is completely monotone on
`(1,∞)`: all sign-corrected derivatives are nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_completeMonotone
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ ((-1 : ℝ) ^ n) *
      iteratedDeriv n
        (fun mu : ℝ =>
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta mu u)
            u)
        lambda := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_iteratedDeriv_eq
    H N hN beta hbeta n lambda hlambda u]
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_isSelfAdjoint
          H N hN beta hbeta lambda hlambda)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_inner_nonneg
          H N hN beta hbeta lambda hlambda)
        n u
  change 0 ≤ s * (s * b)
  calc
    0 ≤ b := hb
    _ = s * (s * b) := by rw [← mul_assoc, hs, one_mul]

/-- Audit-visible package for the completed above-one analytic and completely
monotone right-resolvent hierarchy. -/
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
  exactScalarDerivatives :
    ∀ (n : ℕ) (lambda : ℝ), 1 < lambda →
      ∀ u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta,
      iteratedDeriv n
          (fun mu : ℝ =>
            inner ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
                H N hN beta hbeta mu u)
              u)
          lambda =
        ((-1 : ℝ) ^ n) *
          ((n.factorial : ℝ) *
            inner ℝ
              ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
                H N hN beta hbeta lambda ^ (n + 1)) u)
              u)
  alternatingOperatorNormBound :
    ∀ (n : ℕ) (lambda : ℝ), 1 < lambda →
      ‖((-1 : ℝ) ^ n) •
          ((n.factorial : ℝ) •
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda) ^ (n + 1))‖ ≤
        (n.factorial : ℝ) * ((lambda - 1)⁻¹) ^ (n + 1)
  completeMonotonicity :
    ∀ (n : ℕ) (lambda : ℝ), 1 < lambda →
      ∀ u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta,
      0 ≤ ((-1 : ℝ) ^ n) *
        iteratedDeriv n
          (fun mu : ℝ =>
            inner ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
                H N hN beta hbeta mu u)
              u)
          lambda

/-- Construct the full above-one complete-monotonicity package. -/
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
    exactScalarDerivatives :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_iteratedDeriv_eq
        H N hN beta hbeta
    alternatingOperatorNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_alternatingFactorialDerivativeValue_norm_le
        H N hN beta hbeta
    completeMonotonicity :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_completeMonotone
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
