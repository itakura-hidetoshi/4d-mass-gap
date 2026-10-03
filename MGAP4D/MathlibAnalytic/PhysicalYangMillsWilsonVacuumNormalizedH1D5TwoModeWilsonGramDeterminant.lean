import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5LiteralPositiveQuadraticObstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical
import Mathlib.Tactic

/-!
# H1-D5 as a literal two-mode Wilson Gram-determinant obstruction

#5041 proves that H1-D5 forces the finite physical one-slab transfer to be a
scalar multiple of one rank-one projector.  Hence every 2 x 2 matrix-coefficient
minor of that transfer must have determinant zero.

This file specializes that elementary rank-one fact to the explicit SU(N)
primary-spatial-plaquette two-mode family from #5000/#5015 and then unfolds each
matrix coefficient into the literal finite one-slab Wilson double integral.

The resulting residual is a single scalar statement:

  I00 * I11 - I01 * I10 = 0,

where Iij is the literal Wilson one-slab kernel pairing of the two explicit
physical one-slice modes.

Therefore any nonzero determinant -- in particular any strictly positive
determinant -- refutes H1-D5.  The statement contains no OS completion,
continuum limit, spectral witness, or top-vector coordinate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5TwoModeDetTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5TwoModeDetCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5TwoModeDetSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5TwoModeDetMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5TwoModeDetBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5TwoModeDetSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5TwoModeDetSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Every two-by-two matrix-coefficient minor of a scalar multiple of a real
self-rank-one operator has determinant zero. -/
theorem real_smul_selfRankOne_two_by_two_matrixCoefficient_det_eq_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (a : ℝ)
    (Omega x y : E) :
    inner ℝ
        ((a • InnerProductSpace.rankOne ℝ Omega Omega) x) x *
      inner ℝ
        ((a • InnerProductSpace.rankOne ℝ Omega Omega) y) y -
      inner ℝ
        ((a • InnerProductSpace.rankOne ℝ Omega Omega) x) y *
      inner ℝ
        ((a • InnerProductSpace.rankOne ℝ Omega Omega) y) x = 0 := by
  simp only [
    ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply,
    smul_smul,
    real_inner_smul_left]
  ring

/-- Literal finite one-slab Wilson coefficient of the explicit physical
primary-plaquette two-mode family. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i j : Fin 2) : ℝ :=
  ∫ p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2 *
      (((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 i :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
        ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 j :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.2)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- The literal coefficient is exactly the physical one-slab matrix
coefficient of the two explicit one-slice modes. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysical_transferInner_eq_literalOneSlabCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i j : Fin 2) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
            H hN2 i))
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 j) =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
        H N hN hN2 beta hbeta i j := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral
      H N hN beta hbeta
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 i)
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 j)

/-- The literal two-mode Wilson Gram determinant. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
      H N hN hN2 beta hbeta 0 0 *
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
      H N hN hN2 beta hbeta 1 1 -
  periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
      H N hN hN2 beta hbeta 0 1 *
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
      H N hN hN2 beta hbeta 1 0

section H1D5TwoModeDeterminant

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- H1-D5 forces the two-by-two physical transfer minor of the explicit
primary-plaquette two-mode family to have determinant zero. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_twoModePhysicalTransferGramDet_eq_zero
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ) :
    let H := halfExtent n
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN (beta n) (hbeta n)
    let u0 :=
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 (0 : Fin 2)
    let u1 :=
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 (1 : Fin 2)
    inner ℝ (T u0) u0 * inner ℝ (T u1) u1 -
      inner ℝ (T u0) u1 * inner ℝ (T u1) u0 = 0 := by
  let H := halfExtent n
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN (beta n) (hbeta n)
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN (beta n) (hbeta n)
  let u0 :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 (0 : Fin 2)
  let u1 :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 (1 : Fin 2)
  have hRank :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_physicalOneSlabTransfer_norm_smul_rankOne
      Q hInvariant C hCompat n
  change
    inner ℝ (T u0) u0 * inner ℝ (T u1) u1 -
      inner ℝ (T u0) u1 * inner ℝ (T u1) u0 = 0
  change
    T =
      ‖T‖ • InnerProductSpace.rankOne ℝ Omega Omega at hRank
  rw [hRank]
  exact
    real_smul_selfRankOne_two_by_two_matrixCoefficient_det_eq_zero
      ‖T‖ Omega u0 u1

/-- H1-D5 therefore forces the completely literal two-mode one-slab Wilson
Gram determinant to vanish. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_literalTwoModeWilsonGramDet_eq_zero
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
        (halfExtent n) N hN hN2 (beta n) (hbeta n) = 0 := by
  have hdet :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_twoModePhysicalTransferGramDet_eq_zero
      Q hInvariant C hCompat n
  dsimp only at hdet
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
  rw [
    ← periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysical_transferInner_eq_literalOneSlabCoefficient
      (halfExtent n) N hN hN2 (beta n) (hbeta n) 0 0,
    ← periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysical_transferInner_eq_literalOneSlabCoefficient
      (halfExtent n) N hN hN2 (beta n) (hbeta n) 1 1,
    ← periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysical_transferInner_eq_literalOneSlabCoefficient
      (halfExtent n) N hN hN2 (beta n) (hbeta n) 0 1,
    ← periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysical_transferInner_eq_literalOneSlabCoefficient
      (halfExtent n) N hN hN2 (beta n) (hbeta n) 1 0]
  exact hdet

/-- A nonzero literal two-mode Wilson Gram determinant at one finite scale
refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_literalTwoModeWilsonGramDet_ne_zero
    (n : ℕ)
    (hne :
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
        (halfExtent n) N hN hN2 (beta n) (hbeta n) ≠ 0) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro hCompat
  exact hne
    (physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_literalTwoModeWilsonGramDet_eq_zero
      Q hInvariant C hCompat n)

/-- Strict positivity is a convenient sufficient scalar witness for the same
obstruction. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_literalTwoModeWilsonGramDet_pos
    (n : ℕ)
    (hpos :
      0 <
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
          (halfExtent n) N hN hN2 (beta n) (hbeta n)) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  exact
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_literalTwoModeWilsonGramDet_ne_zero
      Q hInvariant C n hpos.ne'

/-- Audit-visible package for the exact two-mode scalar obstruction. -/
structure PhysicalYangMillsVacuumNormalizedH1D5TwoModeWilsonGramDeterminantPackage : Prop where
  compatibilityForcesZero :
    ∀ (_hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C),
      ∀ n : ℕ,
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
          (halfExtent n) N hN hN2 (beta n) (hbeta n) = 0
  nonzeroDeterminantObstructs :
    ∀ n : ℕ,
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
          (halfExtent n) N hN hN2 (beta n) (hbeta n) ≠ 0 →
        ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C

theorem physicalYangMillsVacuumNormalizedH1D5TwoModeWilsonGramDeterminantPackage :
    PhysicalYangMillsVacuumNormalizedH1D5TwoModeWilsonGramDeterminantPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { compatibilityForcesZero := by
      intro hCompat n
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_literalTwoModeWilsonGramDet_eq_zero
          Q hInvariant C hCompat n
    nonzeroDeterminantObstructs := by
      intro n hne
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_literalTwoModeWilsonGramDet_ne_zero
          Q hInvariant C n hne }

end H1D5TwoModeDeterminant

end

end MathlibAnalytic
end MGAP4D
