import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventTaylorNeumann
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Evaluation of a bounded real-Hilbert endomorphism against a fixed vector
in the same quadratic form.  This is the continuous linear functional
`A ↦ ⟪A u, u⟫_ℝ` on the Banach space of bounded endomorphisms. -/
noncomputable def realContinuousLinearMap_quadraticEvaluation
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (u : E) :
    (E →L[ℝ] E) →L[ℝ] ℝ :=
  ({ toFun := fun A : E →L[ℝ] E => inner ℝ (A u) u
     map_add' := by
       intro A B
       simp only [ContinuousLinearMap.add_apply, inner_add_left]
     map_smul' := by
       intro c A
       simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left,
         RingHom.id_apply] } :
      (E →L[ℝ] E) →ₗ[ℝ] ℝ).mkContinuous
    (‖u‖ ^ 2)
    (by
      intro A
      calc
        ‖inner ℝ (A u) u‖ ≤ ‖A u‖ * ‖u‖ := norm_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg u)
        _ = (‖u‖ ^ 2) * ‖A‖ := by ring)

@[simp]
theorem realContinuousLinearMap_quadraticEvaluation_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (u : E)
    (A : E →L[ℝ] E) :
    realContinuousLinearMap_quadraticEvaluation u A = inner ℝ (A u) u :=
  rfl

/-- A derivative of an operator-valued curve descends through a fixed
quadratic evaluation functional. -/
theorem HasDerivAt.quadraticEvaluation
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {F : ℝ → (E →L[ℝ] E)}
    {F' : E →L[ℝ] E}
    {lambda : ℝ}
    (hF : HasDerivAt F F' lambda)
    (u : E) :
    HasDerivAt
      (fun mu : ℝ => inner ℝ (F mu u) u)
      (inner ℝ (F' u) u)
      lambda := by
  have hcomp :=
    (realContinuousLinearMap_quadraticEvaluation u).hasFDerivAt.comp_hasDerivAt
      lambda hF
  simpa only [Function.comp_apply,
    realContinuousLinearMap_quadraticEvaluation_apply] using hcomp

/-- The within-set version of fixed quadratic evaluation. -/
theorem HasDerivWithinAt.quadraticEvaluation
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {F : ℝ → (E →L[ℝ] E)}
    {F' : E →L[ℝ] E}
    {s : Set ℝ}
    {lambda : ℝ}
    (hF : HasDerivWithinAt F F' s lambda)
    (u : E) :
    HasDerivWithinAt
      (fun mu : ℝ => inner ℝ (F mu u) u)
      (inner ℝ (F' u) u)
      s lambda := by
  have hcomp :=
    (realContinuousLinearMap_quadraticEvaluation u).hasFDerivAt.comp_hasDerivWithinAt
      lambda hF
  simpa only [Function.comp_apply,
    realContinuousLinearMap_quadraticEvaluation_apply] using hcomp

/-- Powers of a positive self-adjoint bounded real-Hilbert endomorphism have
nonnegative quadratic forms.  The proof is elementary: the two-step recursion
`A^(k+2) = A * A^k * A` moves the leftmost `A` through the real inner product
by symmetry and reduces positivity at level `k+2` to positivity at level `k`
on the vector `A u`. -/
theorem realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hself : IsSelfAdjoint A)
    (hpos : ∀ u : E, 0 ≤ inner ℝ (A u) u)
    (n : ℕ)
    (u : E) :
    0 ≤ inner ℝ ((A ^ n) u) u := by
  have hsymm : A.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rcases n with _ | n
      · simpa [real_inner_self_eq_norm_sq] using sq_nonneg ‖u‖
      · rcases n with _ | k
        · simpa using hpos u
        · have hpow : A ^ (k + 2) = A * (A ^ k) * A := by
            calc
              A ^ (k + 2) = A ^ (k + 1) * A := by
                simpa [Nat.add_assoc] using pow_succ A (k + 1)
              _ = (A * A ^ k) * A := by
                rw [show k + 1 = 1 + k by omega, pow_add, pow_one]
          rw [hpow]
          change 0 ≤ inner ℝ (A ((A ^ k) (A u))) u
          rw [hsymm ((A ^ k) (A u)) u]
          exact ih k (by omega) (A u)

/-- Factorial-weighted powers of a positive self-adjoint bounded endomorphism
remain quadratically nonnegative. -/
theorem realContinuousLinearMap_factorial_mul_pow_inner_nonneg
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hself : IsSelfAdjoint A)
    (hpos : ∀ u : E, 0 ≤ inner ℝ (A u) u)
    (n : ℕ)
    (u : E) :
    0 ≤ (n.factorial : ℝ) * inner ℝ ((A ^ (n + 1)) u) u := by
  exact mul_nonneg (by positivity)
    (realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
      A hself hpos (n + 1) u)

/-- Fixed-vector quadratic matrix elements inherit the factorial derivative
recurrence of an operator-valued resolvent. -/
theorem resolvent_quadratic_factorialDerivativeStep_hasDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (n : ℕ)
    {lambda : ℝ}
    (hres : HasDerivAt res (res lambda ^ 2) lambda)
    (u : E) :
    HasDerivAt
      (fun mu : ℝ =>
        (n.factorial : ℝ) * inner ℝ ((res mu ^ (n + 1)) u) u)
      (((n + 1).factorial : ℝ) *
        inner ℝ ((res lambda ^ (n + 2)) u) u)
      lambda := by
  have hop :=
    resolvent_factorialDerivativeStep_hasDerivAt res n hres
  have hquad := hop.quadraticEvaluation u
  simpa only [ContinuousLinearMap.smul_apply, real_inner_smul_left,
    Nat.cast_ofNat] using hquad

/-- Within an open below-gap interval, fixed-vector quadratic matrix elements
inherit the same factorial derivative recurrence. -/
theorem resolvent_quadratic_factorialDerivativeStep_hasDerivWithinAt
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (gap : ℝ)
    (hres :
      ∀ {lambda : ℝ}, lambda < gap →
        HasDerivWithinAt res (res lambda ^ 2) (Set.Iio gap) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda < gap)
    (u : E) :
    HasDerivWithinAt
      (fun mu : ℝ =>
        (n.factorial : ℝ) * inner ℝ ((res mu ^ (n + 1)) u) u)
      (((n + 1).factorial : ℝ) *
        inner ℝ ((res lambda ^ (n + 2)) u) u)
      (Set.Iio gap)
      lambda := by
  have hpow :=
    resolvent_pow_hasDerivWithinAt res gap hres (n + 1) hlambda
  have hscaled :
      HasDerivWithinAt
        (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
        ((n.factorial : ℝ) •
          (((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2)))
        (Set.Iio gap) lambda := by
    simpa only [Pi.smul_apply] using
      (HasDerivWithinAt.const_smul
        (𝕜 := ℝ) (R := ℝ) (F := E →L[ℝ] E)
        (n.factorial : ℝ) hpow)
  have hquad := hscaled.quadraticEvaluation u
  simpa [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    smul_smul, real_inner_smul_left, mul_assoc, mul_comm, mul_left_comm,
    Nat.add_assoc] using hquad

/-- Exact all-order derivative formula for a fixed-vector quadratic resolvent
matrix element on an open real below-gap interval. -/
theorem resolvent_quadratic_iteratedDerivWithin_eq_factorial
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (gap : ℝ)
    (hres :
      ∀ {lambda : ℝ}, lambda < gap →
        HasDerivWithinAt res (res lambda ^ 2) (Set.Iio gap) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda < gap)
    (u : E) :
    iteratedDerivWithin n
        (fun mu : ℝ => inner ℝ (res mu u) u)
        (Set.Iio gap) lambda =
      (n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (fun mu : ℝ => inner ℝ (res mu u) u)
                (Set.Iio gap))
              (Set.Iio gap) lambda =
            derivWithin
              (fun mu : ℝ =>
                (n.factorial : ℝ) * inner ℝ ((res mu ^ (n + 1)) u) u)
              (Set.Iio gap) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hstep :=
        resolvent_quadratic_factorialDerivativeStep_hasDerivWithinAt
          res gap hres n hlambda u
      exact hstep.derivWithin (isOpen_Iio.uniqueDiffOn lambda hlambda)

/-- Ordinary all-order derivative formula for the fixed-vector quadratic
resolvent matrix element at every point strictly below the gap. -/
theorem resolvent_quadratic_iteratedDeriv_eq_factorial
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (res : ℝ → (E →L[ℝ] E))
    (gap : ℝ)
    (hres :
      ∀ {lambda : ℝ}, lambda < gap →
        HasDerivWithinAt res (res lambda ^ 2) (Set.Iio gap) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda < gap)
    (u : E) :
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
      (n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u := by
  calc
    iteratedDeriv n (fun mu : ℝ => inner ℝ (res mu u) u) lambda =
        iteratedDerivWithin n
          (fun mu : ℝ => inner ℝ (res mu u) u)
          (Set.Iio gap) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := fun mu : ℝ => inner ℝ (res mu u) u)
        isOpen_Iio hlambda).symm
    _ = (n.factorial : ℝ) * inner ℝ ((res lambda ^ (n + 1)) u) u :=
      resolvent_quadratic_iteratedDerivWithin_eq_factorial
        res gap hres n hlambda u

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicitySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicityPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Fixed-vector scalar quadratic matrix element of the completed
proof-independent resolvent family. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (lambda : ℝ) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
      H N hN beta hbeta lambda u)
    u

/-- Below the gap, the proof-independent completed resolvent is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta lambda) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
    H N hN beta hbeta lambda hlambda]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_isSelfAdjoint
      H N hN beta hbeta lambda hlambda

/-- Below the gap, the proof-independent completed resolvent has nonnegative
quadratic form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta lambda u)
      u := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
    H N hN beta hbeta lambda hlambda]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_inner_nonneg
      H N hN beta hbeta lambda hlambda u

/-- Every power of the completed below-gap resolvent has nonnegative fixed
quadratic form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_pow_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (n : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta lambda ^ n) u)
      u := by
  exact
    realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_isSelfAdjoint
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_inner_nonneg
        H N hN beta hbeta lambda hlambda)
      n u

/-- The scalar quadratic resolvent amplitude has the exact all-order
factorial derivative formula. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
          H N hN beta hbeta u)
        lambda =
      (n.factorial : ℝ) *
        inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda ^ (n + 1)) u)
          u := by
  let gap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
      H N hN beta hbeta
  let res :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
      H N hN beta hbeta
  have hres :
      ∀ {mu : ℝ}, mu < gap →
        HasDerivWithinAt res (res mu ^ 2) (Set.Iio gap) mu := by
    intro mu hmu
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasDerivAt
        H N hN beta hbeta mu hmu).hasDerivWithinAt
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude,
    res, gap] using
    resolvent_quadratic_iteratedDeriv_eq_factorial
      res gap hres n hlambda u

/-- All ordinary derivatives of every fixed-vector completed below-gap
resolvent quadratic amplitude are nonnegative: the amplitude is absolutely
monotone on the open interval below the explicit finite-volume gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_iteratedDeriv_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    0 ≤ iteratedDeriv n
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
        H N hN beta hbeta u)
      lambda := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    H N hN beta hbeta u n lambda hlambda]
  exact mul_nonneg (by positivity)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_pow_inner_nonneg
      H N hN beta hbeta lambda hlambda (n + 1) u)

/-- Audit-visible package for the completed finite-volume quadratic-resolvent
absolute-monotonicity hierarchy. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  resolventSelfAdjoint :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      IsSelfAdjoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda)
  resolventPowerQuadraticNonnegative :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (n : ℕ)
      (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      0 ≤ inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda ^ n) u)
        u
  quadraticIteratedDerivativeFormula :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      (n : ℕ)
      (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      iteratedDeriv n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
            H N hN beta hbeta u)
          lambda =
        (n.factorial : ℝ) *
          inner ℝ
            ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta lambda ^ (n + 1)) u)
            u
  quadraticAbsoluteMonotonicity :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      (n : ℕ)
      (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      0 ≤ iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
          H N hN beta hbeta u)
        lambda

/-- Construct the completed finite-volume quadratic-resolvent
absolute-monotonicity package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicityPackage
      H N hN beta hbeta := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_isSelfAdjoint
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_pow_inner_nonneg
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_iteratedDeriv_nonneg
        H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
