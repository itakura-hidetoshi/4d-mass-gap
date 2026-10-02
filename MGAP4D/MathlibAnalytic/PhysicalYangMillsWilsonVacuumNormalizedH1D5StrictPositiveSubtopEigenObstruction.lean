import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5PhysicalOperatorPowerCriterion
import MGAP4D.MathlibAnalytic.ContinuousRealLinearOperatorExpEigenvector
import Mathlib.Tactic

/-!
# Strict-positive subtop eigenmode obstruction to H1-D5

The preceding finite-volume reduction identifies H1-D5 with the raw physical
one-slab polynomial identity

`T^(H+3) = ‖T‖² T^(H+1)`.

This file records the immediate spectral consequence without adding any model
assumption.

For any bounded real-linear operator, if

`T^(m+2) = ‖T‖² T^m`

and a nonzero vector satisfies `T f = rho • f` with `rho > 0`, then
`rho = ‖T‖`.  Therefore any strictly positive eigenvalue below the top norm is
an exact obstruction to H1-D5.

The remaining model-facing question is only whether the concrete finite Wilson
physical transfer theorem-generates such a strictly positive subtop mode.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- A positive nonzero eigenvalue of an operator satisfying the H1-D5-type
power identity must equal the operator norm. -/
theorem realContinuousLinearMap_powerIdentity_positiveEigenvalue_eq_norm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (m : ℕ)
    (f : E)
    (rho : ℝ)
    (hf : f ≠ 0)
    (hrho : 0 < rho)
    (hEigen : T f = rho • f)
    (hPower :
      T ^ (m + 2) = (‖T‖ ^ 2) • (T ^ m)) :
    rho = ‖T‖ := by
  have hHigh :=
    realContinuousLinearMap_pow_apply_of_apply_eq_smul
      T f rho hEigen (m + 2)
  have hLow :=
    realContinuousLinearMap_pow_apply_of_apply_eq_smul
      T f rho hEigen m
  have hApply :=
    congrArg (fun A : E →L[ℝ] E => A f) hPower
  change
    (T ^ (m + 2)) f =
      (‖T‖ ^ 2) • ((T ^ m) f) at hApply
  rw [hHigh, hLow, smul_smul] at hApply
  have hInner :=
    congrArg (fun z : E => inner ℝ z f) hApply
  simp only [real_inner_smul_left] at hInner
  have hff : 0 < inner ℝ f f :=
    real_inner_self_pos.mpr hf
  have hScalar :
      rho ^ (m + 2) =
        (‖T‖ ^ 2) * rho ^ m := by
    exact mul_right_cancel₀ (ne_of_gt hff) hInner
  have hrhoPow : rho ^ m ≠ 0 :=
    pow_ne_zero m (ne_of_gt hrho)
  have hSq : rho ^ 2 = ‖T‖ ^ 2 := by
    apply mul_left_cancel₀ hrhoPow
    calc
      rho ^ m * rho ^ 2 = rho ^ (m + 2) := by
        exact (pow_add rho m 2).symm
      _ = (‖T‖ ^ 2) * rho ^ m := hScalar
      _ = rho ^ m * ‖T‖ ^ 2 := by ring
  have hNorm : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith

/-- A strictly positive eigenvalue strictly below the operator norm contradicts
the H1-D5-type power identity. -/
theorem realContinuousLinearMap_powerIdentity_ne_of_strictPositiveSubtopEigenmode
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (m : ℕ)
    (f : E)
    (rho : ℝ)
    (hf : f ≠ 0)
    (hrho : 0 < rho)
    (hrhoTop : rho < ‖T‖)
    (hEigen : T f = rho • f) :
    T ^ (m + 2) ≠ (‖T‖ ^ 2) • (T ^ m) := by
  intro hPower
  have hEq :=
    realContinuousLinearMap_powerIdentity_positiveEigenvalue_eq_norm
      T m f rho hf hrho hEigen hPower
  exact (ne_of_lt hrhoTop) hEq

section PhysicalWilsonH1D5Obstruction

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- H1-D5 forces every strictly positive finite-volume physical one-slab
eigenvalue to be the top eigenvalue. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_positiveEigenvalue_eq_topNorm
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ)
    (rho : ℝ)
    (f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N)
    (hf : f ≠ 0)
    (hrho : 0 < rho)
    (hEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) f =
        rho • f) :
    rho =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ := by
  let H := halfExtent n
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN (beta n) (hbeta n)
  have hPower :=
    (physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_physicalOneSlabPowerIdentity_explicit
      Q hInvariant C).1 hCompat n
  change
    T ^ (H + 3) =
      (‖T‖ ^ 2) • (T ^ (H + 1)) at hPower
  have hPower' :
      T ^ ((H + 1) + 2) =
        (‖T‖ ^ 2) • (T ^ (H + 1)) := by
    rw [show (H + 1) + 2 = H + 3 by omega]
    exact hPower
  change T f = rho • f at hEigen
  exact
    realContinuousLinearMap_powerIdentity_positiveEigenvalue_eq_norm
      T (H + 1) f rho hf hrho hEigen hPower'

/-- A concrete strictly positive subtop eigenmode at even one finite scale
refutes H1-D5, and hence refutes the last compatibility seam remaining after
H1-D4 and H1-D6 were eliminated. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_strictPositiveSubtopEigenmode
    (n : ℕ)
    (rho : ℝ)
    (f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N)
    (hf : f ≠ 0)
    (hrho : 0 < rho)
    (hrhoTop :
      rho <
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖)
    (hEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) f =
        rho • f) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro hCompat
  have hEq :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_positiveEigenvalue_eq_topNorm
      Q hInvariant C hCompat n rho f hf hrho hEigen
  exact (ne_of_lt hrhoTop) hEq

/-- Audit-visible statement of the exact remaining spectral obstruction. -/
structure PhysicalYangMillsVacuumNormalizedH1D5StrictPositiveSubtopObstructionPackage : Prop where
  positiveEigenvalueRigidity :
    ∀ (_hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
      (n : ℕ) (rho : ℝ)
      (f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N),
      f ≠ 0 →
      0 < rho →
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) f = rho • f →
      rho =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖
  strictSubtopRefutes :
    ∀ (n : ℕ) (rho : ℝ)
      (f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N),
      f ≠ 0 →
      0 < rho →
      rho <
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖ →
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) f = rho • f →
      ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C

theorem physicalYangMillsVacuumNormalizedH1D5StrictPositiveSubtopObstructionPackage :
    PhysicalYangMillsVacuumNormalizedH1D5StrictPositiveSubtopObstructionPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { positiveEigenvalueRigidity := by
      intro hCompat n rho f hf hrho hEigen
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_positiveEigenvalue_eq_topNorm
          Q hInvariant C hCompat n rho f hf hrho hEigen
    strictSubtopRefutes := by
      intro n rho f hf hrho hrhoTop hEigen
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_strictPositiveSubtopEigenmode
          Q hInvariant C n rho f hf hrho hrhoTop hEigen }

end PhysicalWilsonH1D5Obstruction

end

end MathlibAnalytic
end MGAP4D
