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
in the same quadratic form. This is the continuous linear functional
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
       change c * inner ℝ (A u) u = c * inner ℝ (A u) u
       rfl } :
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
nonnegative quadratic forms. The proof uses the two-step recursion
`A^(k+2) = A * A^k * A`: self-adjointness moves the leftmost `A` across the
inner product and reduces positivity at level `k+2` to positivity at level `k`
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
          have hs :
              inner ℝ (A ((A ^ k) (A u))) u =
                inner ℝ ((A ^ k) (A u)) (A u) := by
            exact hsymm ((A ^ k) (A u)) u
          rw [hs]
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
  have hquad := HasDerivAt.quadraticEvaluation hop u
  simpa only [ContinuousLinearMap.smul_apply, real_inner_smul_left] using hquad

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
  have hquad := HasDerivWithinAt.quadraticEvaluation hscaled u
  simpa [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    smul_smul, real_inner_smul_left, mul_assoc, mul_comm, mul_left_comm,
    Nat.add_assoc] using hquad

/-- Exact all-order derivative formula for a fixed-vector quadratic resolvent
matrix element on an abstract open real below-gap interval. This generic theorem
keeps all iterated-derivative normalization away from dependent concrete
carriers. -/
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
resolvent matrix element on an abstract carrier. -/
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

/-- The base scalar quadratic amplitude is differentiable below the gap, with
derivative equal to the quadratic form of the squared resolvent. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    HasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
        H N hN beta hbeta u)
      (inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda ^ 2) u)
        u)
      lambda := by
  have hR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasDerivAt
      H N hN beta hbeta lambda hlambda
  have hquad := HasDerivAt.quadraticEvaluation hR u
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude] using hquad

/-- Fundamental all-order scalar derivative hierarchy on the completed
carrier. For every `n`, differentiating the `n! R^(n+1)` quadratic value gives
the next factorial value. This avoids concrete `iteratedDeriv` normalization
while retaining the full mathematical derivative tower. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_factorialDerivativeStep_hasDerivAt
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
    HasDerivAt
      (fun mu : ℝ =>
        (n.factorial : ℝ) *
          inner ℝ
            ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta mu ^ (n + 1)) u)
            u)
      (((n + 1).factorial : ℝ) *
        inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda ^ (n + 2)) u)
          u)
      lambda := by
  exact
    resolvent_quadratic_factorialDerivativeStep_hasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta)
      n
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasDerivAt
        H N hN beta hbeta lambda hlambda)
      u

/-- Every value in the completed scalar factorial derivative hierarchy is
nonnegative below the gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_factorialDerivativeValue_nonneg
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
    0 ≤ (n.factorial : ℝ) *
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda ^ (n + 1)) u)
        u := by
  exact mul_nonneg (by positivity)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_pow_inner_nonneg
      H N hN beta hbeta lambda hlambda (n + 1) u)

/-- The derivative value in every step of the completed scalar hierarchy is
nonnegative. This is the fundamental receipt of below-gap absolute
monotonicity without forcing Lean to normalize `iteratedDeriv` on the huge
dependent carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_factorialDerivativeStep_value_nonneg
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
    0 ≤ ((n + 1).factorial : ℝ) *
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda ^ (n + 2)) u)
        u := by
  simpa only [Nat.add_assoc] using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_factorialDerivativeValue_nonneg
      H N hN beta hbeta u (n + 1) lambda hlambda

/-- Audit-visible package for the completed finite-volume quadratic-resolvent
positive derivative hierarchy. The exact ordinary `iteratedDeriv` formula is
proved generically above; the concrete carrier records the fundamental
`HasDerivAt` recurrence and nonnegative derivative values to avoid dependent
carrier normalization timeouts. -/
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
  quadraticBaseDerivative :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      HasDerivAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude
          H N hN beta hbeta u)
        (inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda ^ 2) u)
          u)
        lambda
  factorialDerivativeStep :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      (n : ℕ)
      (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      HasDerivAt
        (fun mu : ℝ =>
          (n.factorial : ℝ) *
            inner ℝ
              ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
                H N hN beta hbeta mu ^ (n + 1)) u)
              u)
        (((n + 1).factorial : ℝ) *
          inner ℝ
            ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta lambda ^ (n + 2)) u)
            u)
        lambda
  factorialDerivativeValueNonnegative :
    ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      (n : ℕ)
      (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      0 ≤ (n.factorial : ℝ) *
        inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda ^ (n + 1)) u)
          u

/-- Construct the completed finite-volume quadratic-resolvent positive
derivative hierarchy package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventQuadraticAbsoluteMonotonicityPackage
      H N hN beta hbeta := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_isSelfAdjoint
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_pow_inner_nonneg
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_hasDerivAt
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_factorialDerivativeStep_hasDerivAt
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventQuadraticAmplitude_factorialDerivativeValue_nonneg
        H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
