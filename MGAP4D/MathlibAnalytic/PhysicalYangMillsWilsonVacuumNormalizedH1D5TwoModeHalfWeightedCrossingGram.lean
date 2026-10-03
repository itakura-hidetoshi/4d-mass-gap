import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeFeatureKernelResidual
import Mathlib.Tactic

/-!
# H1-D5 two-mode residual as a half-weighted temporal-crossing Gram determinant

The literal one-slab kernel used by #5043 is definitionally the symmetric
spatial-half-weight sandwich of the temporal-gauge crossing kernel,

  K_slab(A,B) = h(A) * K_cross(A,B) * h(B).

This file pushes that factorization all the way through the explicit physical
two-mode 2 x 2 minor.  No positivity argument is added here: the point is to
put the remaining scalar obstruction in exactly the form needed by the existing
positive-density/Fock strictness machinery.

Thus H1-D5 is refuted as soon as the half-weighted crossing-kernel Gram
determinant of the two explicit physical Wilson modes is nonzero (or positive).
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5TwoModeCrossingTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5TwoModeCrossingCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5TwoModeCrossingSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5TwoModeCrossingMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5TwoModeCrossingBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5TwoModeCrossingSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Temporal-crossing matrix coefficient after absorbing the two strictly
positive spatial half-weights into the explicit physical modes. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
    (H N : ℕ)
    (_hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (_hbeta : 0 ≤ beta)
    (i j : Fin 2) : ℝ :=
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ui : Lp ℝ 2 μ :=
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 i :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  let uj : Lp ℝ 2 μ :=
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 j :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  ∫ p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta p.1 p.2 *
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
        H N beta p.1 * ui p.1) *
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
        H N beta p.2 * uj p.2)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- The literal one-slab coefficient from #5043 is exactly the half-weighted
crossing-kernel coefficient. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_halfWeightedCrossingCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i j : Fin 2) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
        H N hN hN2 beta hbeta i j =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
        H N hN hN2 beta hbeta i j := by
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
  apply integral_congr_ae
  filter_upwards [] with p
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  ring

/-- The 2 x 2 determinant after moving the spatial half-weights from the
one-slab kernel into the two explicit physical modes. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 0 0 *
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 1 1 -
  periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 0 1 *
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 1 0

/-- Exact scalar bridge from the one-slab determinant to the temporal-crossing
determinant with positive endpoint reweighting. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_eq_halfWeightedCrossingGramDet
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
        H N hN hN2 beta hbeta =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
        H N hN hN2 beta hbeta := by
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
  rw [
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_halfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 0 0,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_halfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 1 1,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_halfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 0 1,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_halfWeightedCrossingCoefficient
      H N hN hN2 beta hbeta 1 0]

section H1D5HalfWeightedCrossing

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

/-- A nonzero half-weighted temporal-crossing two-mode determinant at one
finite scale refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_halfWeightedCrossingGramDet_ne_zero
    (n : ℕ)
    (hne :
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
        (halfExtent n) N hN hN2 (beta n) (hbeta n) ≠ 0) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  apply
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_literalTwoModeWilsonGramDet_ne_zero
      (hN2 := hN2) Q hInvariant C n
  rwa [
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_eq_halfWeightedCrossingGramDet
      (halfExtent n) N hN hN2 (beta n) (hbeta n)]

/-- Strict positivity of the same crossing determinant is a convenient
sufficient witness. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_halfWeightedCrossingGramDet_pos
    (n : ℕ)
    (hpos :
      0 <
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
          (halfExtent n) N hN hN2 (beta n) (hbeta n)) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  exact
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_halfWeightedCrossingGramDet_ne_zero
      (hN2 := hN2) Q hInvariant C n hpos.ne'

end H1D5HalfWeightedCrossing

end

end MathlibAnalytic
end MGAP4D
