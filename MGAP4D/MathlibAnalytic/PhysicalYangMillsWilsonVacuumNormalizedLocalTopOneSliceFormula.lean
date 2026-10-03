import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedPairPositiveHalfTransferRatio
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical
import Mathlib.Tactic

/-!
# One-slice formula for the local projected-top coefficient

PR #5075 removes the finite partition normalization from canonical-sign OS
vacuum-pair coefficients:

  <v_OS, x tensor y>
    = gamma * <S_half x, y>,

with gamma = <v_OS, omega tensor omega>.

The explicit uncentered Wilson two-mode pair from #5015 is exactly

  f_k tensor 1

in ordered endpoint coordinates.  Therefore the local top coefficient of the
actual vacuum-centered pair has the exact one-slice formula

  a_k
    = alpha_k * delta - gamma^2 * m_k,

where
- alpha_k = <omega, f_k>,
- delta   = <omega, 1>,
- gamma   = <v_OS, omega tensor omega>,
- m_k     = <S_half f_k, 1>.

This is an identity at each finite scale.  No completed H1-D5 compatibility,
vacuum/top alignment, continuum dynamics, or limiting statement is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance localTopOneSliceTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance localTopOneSliceCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance localTopOneSliceSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance localTopOneSliceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance localTopOneSliceBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance localTopOneSliceSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance localTopOneSliceSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section LocalTopOneSlice

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- One-slice overlap of the physical top mode with the selected primary
plaquette Wilson mode. -/
noncomputable def
    physicalYangMillsSUNTwoModePrimaryTopCoefficient
    (k : Fin 2) (n : ℕ) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      (halfExtent n) N hN (beta n) (hbeta n))
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      (halfExtent n) hN2 k)

/-- One-slice overlap of the physical top mode with the constant unit vector. -/
noncomputable def
    physicalYangMillsSUNPhysicalTopConstantCoefficient
    (n : ℕ) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      (halfExtent n) N hN (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent n) N)

/-- Finite canonical-sign OS-vacuum / physical pair-top overlap. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSUNVacuumPairTopOverlap
    (n : ℕ) : ℝ :=
  inner ℝ
    (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      (halfExtent n) N hN (beta n) (hbeta n))

/-- Normalized complete positive-half transfer coefficient from the selected
primary Wilson mode to the constant endpoint vector. -/
noncomputable def
    physicalYangMillsSUNTwoModeNormalizedPositiveHalfToConstantCoefficient
    (k : Fin 2) (n : ℕ) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        (halfExtent n) hN2 k))
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent n) N)

/-- The explicit uncentered pair is exactly the physical decomposable pair
f_k tensor 1. -/
theorem
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2_eq_physicalDecomposable
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
        (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        (halfExtent n) N
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          (halfExtent n) hN2 k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          (halfExtent n) N) := by
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_eq_physicalDecomposable
      (halfExtent n) hN2 k

/-- Pair-top pairing against the uncentered mode factors into the product of
the two one-slice top overlaps. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_inner_explicitUncentered_eq_mul_oneSlice
    (k : Fin 2) (n : ℕ) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n))
        (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
          (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) =
      physicalYangMillsSUNTwoModePrimaryTopCoefficient
          (hN := hN) (hN2 := hN2) (beta := beta) (hbeta := hbeta) k n *
        physicalYangMillsSUNPhysicalTopConstantCoefficient
          (hN := hN) (beta := beta) (hbeta := hbeta) n := by
  let H := halfExtent n
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
      H N hN (beta n) (hbeta n)
  let f :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 k
  let one :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  rw [
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2_eq_physicalDecomposable
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n]
  change
    inner ℝ
        (realL2ExternalTensor omega omega)
        (realL2ExternalTensor
          (f : Lp ℝ 2 mu) (one : Lp ℝ 2 mu)) =
      _
  rw [realL2ExternalTensor_inner]
  rfl

/-- The canonical OS-vacuum coefficient of the explicit uncentered pair is the
vacuum/top overlap times the normalized one-slice positive-half coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSUNOSVacuumPair_inner_explicitUncentered_eq_vacuumTopOverlap_mul_normalizedPositiveHalf
    (k : Fin 2) (n : ℕ) :
    inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
          (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) =
      physicalYangMillsVacuumNormalizedSUNVacuumPairTopOverlap
          (hN := hN) (beta := beta) (hbeta := hbeta)
          Q hInvariant n *
        physicalYangMillsSUNTwoModeNormalizedPositiveHalfToConstantCoefficient
          (hN := hN) (hN2 := hN2) (beta := beta) (hbeta := hbeta) k n := by
  rw [
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2_eq_physicalDecomposable
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n]
  exact
    physicalYangMillsVacuumNormalizedSUNOSVacuumPair_inner_physicalPairDecomposable_eq_vacuumTopOverlap_mul_normalizedPositiveHalf
      Q hInvariant n
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        (halfExtent n) hN2 k)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
        (halfExtent n) N)

/-- Exact finite one-slice normal form of the local projected-top coefficient
from #5074.

The entire pair-Haar geometry is reduced to three elementary one-slice
overlaps and one normalized positive-half transfer coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient_eq_oneSlice
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient
        (hN2 := hN2) Q hInvariant k n =
      physicalYangMillsSUNTwoModePrimaryTopCoefficient
          (hN := hN) (hN2 := hN2) (beta := beta) (hbeta := hbeta) k n *
        physicalYangMillsSUNPhysicalTopConstantCoefficient
          (hN := hN) (beta := beta) (hbeta := hbeta) n -
      (physicalYangMillsVacuumNormalizedSUNVacuumPairTopOverlap
          (hN := hN) (beta := beta) (hbeta := hbeta)
          Q hInvariant n) ^ 2 *
        physicalYangMillsSUNTwoModeNormalizedPositiveHalfToConstantCoefficient
          (hN := hN) (hN2 := hN2) (beta := beta) (hbeta := hbeta) k n := by
  unfold physicalYangMillsVacuumNormalizedSUNTwoModeProjectedTopCoefficient
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopPair_inner_eq
      Q hInvariant k n]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_inner_explicitUncentered_eq_mul_oneSlice
      (halfExtent := halfExtent) (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta) k n]
  rw [
    physicalYangMillsVacuumNormalizedSUNOSVacuumPair_inner_explicitUncentered_eq_vacuumTopOverlap_mul_normalizedPositiveHalf
      Q hInvariant k n]
  have hcomm :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) N hN (beta n) (hbeta n))
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n) =
        physicalYangMillsVacuumNormalizedSUNVacuumPairTopOverlap
          (hN := hN) (beta := beta) (hbeta := hbeta)
          Q hInvariant n := by
    simpa [
      physicalYangMillsVacuumNormalizedSUNVacuumPairTopOverlap
    ] using
      (real_inner_comm
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n))
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n))
  rw [hcomm]
  ring

end LocalTopOneSlice

end

end MathlibAnalytic
end MGAP4D
