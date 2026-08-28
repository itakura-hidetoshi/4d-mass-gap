import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventDifferentiability
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- In a real normed Banach algebra, the inverse of the affine shift
`G - lambda • 1` is real analytic at every parameter where the shift is a
unit. This is the abstract analytic resolvent receipt. -/
theorem ringInverse_sub_smul_one_analyticAt
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda : ℝ)
    (hunit : IsUnit (G - lambda • (1 : R))) :
    AnalyticAt ℝ
      (fun mu : ℝ => Ring.inverse (G - mu • (1 : R)))
      lambda := by
  have hconst : AnalyticAt ℝ (fun _ : ℝ => G) lambda := analyticAt_const
  have hid : AnalyticAt ℝ (fun mu : ℝ => mu) lambda := analyticAt_id
  have hone : AnalyticAt ℝ (fun _ : ℝ => (1 : R)) lambda := analyticAt_const
  have hsmul : AnalyticAt ℝ (fun mu : ℝ => mu • (1 : R)) lambda :=
    hid.smul hone
  have hshift :
      AnalyticAt ℝ (fun mu : ℝ => G - mu • (1 : R)) lambda :=
    hconst.sub hsmul
  have hinverse :
      AnalyticAt ℝ Ring.inverse (G - lambda • (1 : R)) := by
    simpa only [hunit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℝ) hunit.unit)
  exact AnalyticAt.comp'
    (𝕜 := ℝ)
    (g := fun x : R => Ring.inverse x)
    (f := fun mu : ℝ => G - mu • (1 : R))
    hinverse hshift

/-- Abstract resolvent-power differentiation within an open below-gap
interval. If `R' = R^2`, then `(R^k)' = k • R^(k+1)`. -/
theorem resolvent_pow_hasDerivWithinAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (gap : ℝ)
    (hres :
      ∀ {lambda : ℝ}, lambda < gap →
        HasDerivWithinAt res (res lambda ^ 2) (Set.Iio gap) lambda)
    (k : ℕ)
    {lambda : ℝ}
    (hlambda : lambda < gap) :
    HasDerivWithinAt
      (fun mu => res mu ^ k)
      ((k : ℝ) • res lambda ^ (k + 1))
      (Set.Iio gap)
      lambda := by
  induction k with
  | zero =>
      simpa using
        (hasDerivWithinAt_const lambda (Set.Iio gap) (1 : A))
  | succ k ih =>
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ)
        (𝔸 := A)
        ih (hres hlambda)
      have hmul' :
          HasDerivWithinAt
            (fun mu => res mu ^ (k + 1))
            ((k : ℝ) • res lambda ^ (k + 1) * res lambda +
              res lambda ^ k * res lambda ^ 2)
            (Set.Iio gap)
            lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((k : ℝ) • res lambda ^ (k + 1) * res lambda +
              res lambda ^ k * res lambda ^ 2) =
            ((Nat.succ k : ℕ) : ℝ) •
              res lambda ^ (Nat.succ k + 1) := by
        let x := res lambda
        change
          ((k : ℝ) • x ^ (k + 1)) * x + x ^ k * x ^ 2 =
            ((Nat.succ k : ℕ) : ℝ) • x ^ (Nat.succ k + 1)
        have hsmul :
            ((k : ℝ) • x ^ (k + 1)) * x =
              (k : ℝ) • (x ^ (k + 1) * x) :=
          Algebra.smul_mul_assoc (k : ℝ) (x ^ (k + 1)) x
        rw [hsmul]
        have hfirst : x ^ (k + 1) * x = x ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ x (k + 1)).symm
        have hsecond : x ^ k * x ^ 2 = x ^ (k + 2) := by
          simpa using (pow_add x k 2).symm
        rw [hfirst, hsecond]
        calc
          (k : ℝ) • x ^ (k + 2) + x ^ (k + 2) =
              (k : ℝ) • x ^ (k + 2) +
                (1 : ℝ) • x ^ (k + 2) := by
            rw [one_smul ℝ]
          _ = ((k : ℝ) + 1) • x ^ (k + 2) :=
            (add_smul (k : ℝ) (1 : ℝ) (x ^ (k + 2))).symm
          _ = ((Nat.succ k : ℕ) : ℝ) •
              x ^ (Nat.succ k + 1) := by
            rw [Nat.cast_succ]
      rw [hderiv] at hmul'
      exact hmul'

/-- Abstract all-order resolvent derivative formula on an open real interval.
The iterated-derivative induction is proved once in an arbitrary real normed
algebra rather than on a large dependent completed carrier. -/
theorem resolvent_iteratedDerivWithin_eq_factorial
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (gap : ℝ)
    (hres :
      ∀ {lambda : ℝ}, lambda < gap →
        HasDerivWithinAt res (res lambda ^ 2) (Set.Iio gap) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda < gap) :
    iteratedDerivWithin n res (Set.Iio gap) lambda =
      (n.factorial : ℝ) • res lambda ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n res (Set.Iio gap))
              (Set.Iio gap) lambda =
            derivWithin
              (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
              (Set.Iio gap) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
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
            (𝕜 := ℝ) (R := ℝ) (F := A)
            (n.factorial : ℝ) hpow)
      have hscaledDeriv :
          derivWithin
              (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
              (Set.Iio gap) lambda =
            (n.factorial : ℝ) •
              (((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2)) :=
        hscaled.derivWithin (isOpen_Iio.uniqueDiffOn lambda hlambda)
      rw [hscaledDeriv]
      simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        smul_smul, mul_comm, Nat.add_assoc]

/-- Ordinary all-order version of the abstract resolvent derivative formula at
interior points of the below-gap interval. -/
theorem resolvent_iteratedDeriv_eq_factorial
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (gap : ℝ)
    (hres :
      ∀ {lambda : ℝ}, lambda < gap →
        HasDerivWithinAt res (res lambda ^ 2) (Set.Iio gap) lambda)
    (n : ℕ)
    {lambda : ℝ}
    (hlambda : lambda < gap) :
    iteratedDeriv n res lambda =
      (n.factorial : ℝ) • res lambda ^ (n + 1) := by
  calc
    iteratedDeriv n res lambda =
        iteratedDerivWithin n res (Set.Iio gap) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n) (f := res) isOpen_Iio hlambda).symm
    _ = (n.factorial : ℝ) • res lambda ^ (n + 1) :=
      resolvent_iteratedDerivWithin_eq_factorial
        res gap hres n hlambda

/-- Pointwise version of the abstract resolvent-power derivative identity. -/
theorem resolvent_pow_hasDerivAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (k : ℕ)
    {lambda : ℝ}
    (hres : HasDerivAt res (res lambda ^ 2) lambda) :
    HasDerivAt
      (fun mu => res mu ^ k)
      ((k : ℝ) • res lambda ^ (k + 1))
      lambda := by
  induction k with
  | zero =>
      simpa using
        (hasDerivAt_const (x := lambda) (c := (1 : A)))
  | succ k ih =>
      have hmul := HasDerivAt.mul
        (𝕜 := ℝ)
        (𝔸 := A)
        ih hres
      have hmul' :
          HasDerivAt
            (fun mu => res mu ^ (k + 1))
            ((k : ℝ) • res lambda ^ (k + 1) * res lambda +
              res lambda ^ k * res lambda ^ 2)
            lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((k : ℝ) • res lambda ^ (k + 1) * res lambda +
              res lambda ^ k * res lambda ^ 2) =
            ((Nat.succ k : ℕ) : ℝ) •
              res lambda ^ (Nat.succ k + 1) := by
        let x := res lambda
        change
          ((k : ℝ) • x ^ (k + 1)) * x + x ^ k * x ^ 2 =
            ((Nat.succ k : ℕ) : ℝ) • x ^ (Nat.succ k + 1)
        have hsmul :
            ((k : ℝ) • x ^ (k + 1)) * x =
              (k : ℝ) • (x ^ (k + 1) * x) :=
          Algebra.smul_mul_assoc (k : ℝ) (x ^ (k + 1)) x
        rw [hsmul]
        have hfirst : x ^ (k + 1) * x = x ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ x (k + 1)).symm
        have hsecond : x ^ k * x ^ 2 = x ^ (k + 2) := by
          simpa using (pow_add x k 2).symm
        rw [hfirst, hsecond]
        calc
          (k : ℝ) • x ^ (k + 2) + x ^ (k + 2) =
              (k : ℝ) • x ^ (k + 2) +
                (1 : ℝ) • x ^ (k + 2) := by
            rw [one_smul ℝ]
          _ = ((k : ℝ) + 1) • x ^ (k + 2) :=
            (add_smul (k : ℝ) (1 : ℝ) (x ^ (k + 2))).symm
          _ = ((Nat.succ k : ℕ) : ℝ) •
              x ^ (Nat.succ k + 1) := by
            rw [Nat.cast_succ]
      rw [hderiv] at hmul'
      exact hmul'

/-- Fundamental factorial recurrence for the formal derivative values of a
resolvent. It packages the step from `n! R^(n+1)` to `(n+1)! R^(n+2)` using
only a pointwise `HasDerivAt R R^2` receipt. -/
theorem resolvent_factorialDerivativeStep_hasDerivAt
    {A : Type*}
    [NormedRing A]
    [NormedAlgebra ℝ A]
    (res : ℝ → A)
    (n : ℕ)
    {lambda : ℝ}
    (hres : HasDerivAt res (res lambda ^ 2) lambda) :
    HasDerivAt
      (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
      (((n + 1).factorial : ℝ) • res lambda ^ (n + 2))
      lambda := by
  have hpow := resolvent_pow_hasDerivAt res (n + 1) hres
  have hscaled :
      HasDerivAt
        (fun mu => (n.factorial : ℝ) • res mu ^ (n + 1))
        ((n.factorial : ℝ) •
          (((n + 1 : ℕ) : ℝ) • res lambda ^ (n + 2)))
        lambda := by
    simpa only [Pi.smul_apply] using
      (HasDerivAt.const_smul
        (𝕜 := ℝ) (R := ℝ) (F := A)
        (n.factorial : ℝ) hpow)
  simpa [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    smul_smul, mul_comm, Nat.add_assoc] using hscaled

/-- A reusable factorial norm estimate for powers of a bounded real
endomorphism. -/
theorem continuousLinearMap_factorial_smul_pow_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (n : ℕ)
    (M : ℝ)
    (hA : ‖A‖ ≤ M) :
    ‖(n.factorial : ℝ) • A ^ (n + 1)‖ ≤
      (n.factorial : ℝ) * M ^ (n + 1) := by
  calc
    ‖(n.factorial : ℝ) • A ^ (n + 1)‖ ≤
        ‖(n.factorial : ℝ)‖ * ‖A ^ (n + 1)‖ :=
      ContinuousLinearMap.opNorm_smul_le
        (n.factorial : ℝ) (A ^ (n + 1))
    _ = (n.factorial : ℝ) * ‖A ^ (n + 1)‖ := by
      rw [Real.norm_natCast]
    _ ≤ (n.factorial : ℝ) * ‖A‖ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (norm_pow_le' A (by omega)) (by positivity)
    _ ≤ (n.factorial : ℝ) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg A) hA (n + 1))
        (by positivity)

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedResolventAnalyticHierarchyPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed finite-volume total shifted Green resolvent is real analytic
at every real parameter strictly below the explicit one-step generator gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_analyticAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    AnalyticAt ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta)
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
    ringInverse_sub_smul_one_analyticAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda hunit

/-- Real analyticity of the completed total resolvent representative on the
whole open below-gap interval. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_analyticOnNhd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta)
      (Set.Iio
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)) := by
  intro lambda hlambda
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_analyticAt
      H N hN beta hbeta lambda hlambda

/-- Fundamental concrete all-order recurrence. For each `n`, the candidate
`n`-th derivative value `n! R^(n+1)` has derivative
`(n+1)! R^(n+2)`. Keeping this as `HasDerivAt` avoids normalizing Mathlib's
derived `iteratedDeriv` predicate on the huge completed dependent carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_factorialDerivativeStep_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    HasDerivAt
      (fun mu =>
        (n.factorial : ℝ) •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta mu) ^ (n + 1))
      (((n + 1).factorial : ℝ) •
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda) ^ (n + 2))
      lambda := by
  have hbase0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasDerivAt
      H N hN beta hbeta lambda hlambda
  have hbase :
      HasDerivAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta)
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda) ^ 2)
        lambda := by
    simpa only [pow_two] using hbase0
  exact
    resolvent_factorialDerivativeStep_hasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta)
      n hbase

/-- The exact formal `n`-th derivative value `n! R^(n+1)` obeys the
factorial inverse-gap operator-norm estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_factorialDerivativeValue_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    ‖(n.factorial : ℝ) •
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda) ^ (n + 1)‖ ≤
      (n.factorial : ℝ) *
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹) ^ (n + 1) := by
  let Rlambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
      H N hN beta hbeta lambda
  have hnorm :
      ‖Rlambda‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹ := by
    dsimp [Rlambda]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
        H N hN beta hbeta lambda hlambda]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta lambda hlambda
  exact
    continuousLinearMap_factorial_smul_pow_norm_le
      Rlambda n
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta - lambda)⁻¹)
      hnorm

/-- Audit-visible package for the completed finite-volume analytic resolvent
hierarchy. The concrete carrier records fundamental analytic and `HasDerivAt`
receipts; the exact Mathlib `iteratedDeriv` factorial formula is proved once by
`resolvent_iteratedDeriv_eq_factorial` in the generic Banach-algebra layer. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchyPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  analyticOnNhd :
    AnalyticOnNhd ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta)
      (Set.Iio
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta))
  factorialDerivativeStep :
    ∀ (n : ℕ) (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      HasDerivAt
        (fun mu =>
          (n.factorial : ℝ) •
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta mu) ^ (n + 1))
        (((n + 1).factorial : ℝ) •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda) ^ (n + 2))
        lambda
  factorialDerivativeValueNormBound :
    ∀ (n : ℕ) (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      ‖(n.factorial : ℝ) •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda) ^ (n + 1)‖ ≤
        (n.factorial : ℝ) *
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹) ^ (n + 1)

/-- The completed finite-volume below-gap resolvent satisfies the full analytic
hierarchy package without unfolding any proof-dependent inverse unit. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchyPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchyPackage
      H N hN beta hbeta := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_analyticOnNhd
        H N hN beta hbeta
  · intro n lambda hlambda
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_factorialDerivativeStep_hasDerivAt
        H N hN beta hbeta n lambda hlambda
  · intro n lambda hlambda
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_factorialDerivativeValue_norm_le
        H N hN beta hbeta n lambda hlambda

end

end MathlibAnalytic
end MGAP4D
