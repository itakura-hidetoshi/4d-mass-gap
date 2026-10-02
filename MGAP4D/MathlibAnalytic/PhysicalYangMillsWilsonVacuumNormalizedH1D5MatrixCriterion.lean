import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedSUNTwoModeFiniteOSSingleSeam
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

/-!
# Matrix-coefficient criterion for the single vacuum-normalized H1-D5 seam

After H1-D4, the physical pair carrier is the Hilbert closure of decomposable
Gauss-law physical tensors and the canonical-sign finite OS vacuum pair lies in
that carrier.

Therefore equality of two physical-pair vectors can be checked only against
the decomposable physical generators.  Applying this to the two vectors in the
remaining H1-D5 seam gives an exact equivalence:

* vector-valued completed-transfer compatibility on the canonical OS vacuum;
* equality of all scalar matrix coefficients against decomposable physical
  endpoint pairs.

The completed OS boundary transfer fixes the vacuum already, so this is also
equivalent to the still simpler coefficient identity saying that the normalized
physical pair transfer preserves every vacuum/decomposable matrix coefficient.

Thus the remaining H1-D5 model theorem is reduced to a literal scalar Wilson
kernel/Fubini identity; no further Hilbert completion or carrier compatibility
is left.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5MatrixTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5MatrixCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5MatrixSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5MatrixMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5MatrixBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5MatrixSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5MatrixSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Two vectors in the completed physical pair carrier are equal as soon as
their inner products against every decomposable physical pair agree.

This is the exact Hilbert-separation principle needed for H1-D5.  The proof
uses the closed kernel of the continuous functional `innerSL ℝ (u-v)` and the
definition of the physical carrier as the topological closure of the
decomposable physical span. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_of_inner_decomposable_eq
    (H N : ℕ)
    {u v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N}
    (hu : u ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N)
    (hv : v ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N)
    (hinner :
      ∀ x y :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
        inner ℝ u
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
              H N x y) =
          inner ℝ v
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
              H N x y)) :
    u = v := by
  let w := u - v
  let phi :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ] ℝ :=
    innerSL ℝ w
  have hw :
      w ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
    exact
      Submodule.sub_mem
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N) hu hv
  have hgen :
      periodicHypercubicEvenSpecialUnitaryPhysicalPairGeneratorSet H N ⊆
        phi.ker := by
    rintro z ⟨⟨x, y⟩, rfl⟩
    change
      inner ℝ w
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) = 0
    dsimp [w]
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (hinner x y)
  have hspan :
      periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N ≤ phi.ker := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan]
    exact Submodule.span_le.2 hgen
  have hcarrier :
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N ≤ phi.ker := by
    change
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).topologicalClosure ≤
        phi.ker
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).topologicalClosure_minimal
        hspan phi.isClosed_ker
  have hwker : w ∈ phi.ker := hcarrier hw
  have hself : inner ℝ w w = 0 := by
    change phi w = 0 at hwker
    exact hwker
  have hwzero : w = 0 := inner_self_eq_zero.mp hself
  exact sub_eq_zero.mp hwzero

section VacuumNormalizedH1D5

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

/-- Scalar matrix-coefficient form of H1-D5.  It tests the two candidate
one-step images of the canonical-sign finite OS vacuum pair only against
decomposable physical endpoint tensors. -/
def PhysicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumPairCompletedTransferMatrixCompatibility :
    Prop :=
  ∀ n : ℕ,
    ∀ x y :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            (halfExtent n) N x y) =
        inner ℝ
          (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
            (halfExtent n) N
            (Q.vacuumNormalized.completedBoundaryTransfer hInvariant C n 2)
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            (halfExtent n) N x y)

/-- H1-D5 vector compatibility implies its decomposable matrix-coefficient
form immediately. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedTransferMatrixCompatibility_of_completedCompatibility
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C) :
    PhysicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumPairCompletedTransferMatrixCompatibility
      Q hInvariant C := by
  intro n x y
  rw [hCompat n]

/-- Conversely, decomposable physical matrix coefficients determine the two
H1-D5 vectors because both lie in the completed physical pair carrier. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_of_completedTransferMatrixCompatibility
    (hMatrix :
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumPairCompletedTransferMatrixCompatibility
        Q hInvariant C) :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  let S2 :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  let K2 :=
    periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
      (halfExtent n) N
      (Q.vacuumNormalized.completedBoundaryTransfer hInvariant C n 2)
  have hvac :
      vac ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
    exact
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_mem_physicalPairCarrier
        Q hInvariant n
  have hS2 :
      S2 vac ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
        (halfExtent n) N hN (beta n) (hbeta n) hvac
  have hK2eq : K2 vac = vac := by
    exact
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_completedBoundaryPairTransfer_fixed
        (Q := Q.vacuumNormalized) C n 2
  have hK2 :
      K2 vac ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
    rw [hK2eq]
    exact hvac
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_of_inner_decomposable_eq
      (halfExtent n) N hS2 hK2
  intro x y
  simpa [vac, S2, K2] using hMatrix n x y

/-- Exact H1-D5 reduction: the original one-vector compatibility is equivalent
to scalar equality on all decomposable physical pair tests. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_matrixCompatibility :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumPairCompletedTransferMatrixCompatibility
        Q hInvariant C := by
  constructor
  · exact
      physicalYangMillsVacuumNormalizedSUNTwoMode_completedTransferMatrixCompatibility_of_completedCompatibility
        Q hInvariant C
  · exact
      physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_of_completedTransferMatrixCompatibility
        Q hInvariant C

/-- Since the completed OS boundary transfer fixes the canonical OS vacuum,
H1-D5 is equivalently the scalar statement that normalized physical pair
transfer preserves every vacuum/decomposable physical matrix coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_normalizedTransfer_pairing_fixed :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          inner ℝ
              (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
                (halfExtent n) N hN (beta n) (hbeta n)
                (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
                  (S := S) (D := D) (halfExtent := halfExtent)
                  (N := N) (hN := hN)
                  (beta := beta) (hbeta := hbeta)
                  (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n))
              (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
                (halfExtent n) N x y) =
            inner ℝ
              (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
                (S := S) (D := D) (halfExtent := halfExtent)
                (N := N) (hN := hN)
                (beta := beta) (hbeta := hbeta)
                (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
              (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
                (halfExtent n) N x y) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_matrixCompatibility]
  constructor
  · intro hMatrix n x y
    have h := hMatrix n x y
    rw [
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_completedBoundaryPairTransfer_fixed
        (Q := Q.vacuumNormalized) C n 2] at h
    exact h
  · intro hPair n x y
    have hFixed :=
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_completedBoundaryPairTransfer_fixed
        (Q := Q.vacuumNormalized) C n 2
    calc
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            (halfExtent n) N x y) =
        inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            (halfExtent n) N x y) :=
        hPair n x y
      _ =
        inner ℝ
          (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
            (halfExtent n) N
            (Q.vacuumNormalized.completedBoundaryTransfer hInvariant C n 2)
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            (halfExtent n) N x y) := by
        rw [hFixed]

/-- Audit-visible scalar reduction package for H1-D5. -/
structure PhysicalYangMillsVacuumNormalizedH1D5MatrixCriterionPackage : Prop where
  completedIffMatrix :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumPairCompletedTransferMatrixCompatibility
        Q hInvariant C

/-- Construct the H1-D5 matrix criterion package. -/
theorem physicalYangMillsVacuumNormalizedH1D5MatrixCriterionPackage :
    PhysicalYangMillsVacuumNormalizedH1D5MatrixCriterionPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { completedIffMatrix :=
      physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_matrixCompatibility
        Q hInvariant C }

end VacuumNormalizedH1D5

end

end MathlibAnalytic
end MGAP4D
