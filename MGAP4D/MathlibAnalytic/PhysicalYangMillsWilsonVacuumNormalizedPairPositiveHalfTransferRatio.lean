import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedProjectedLocalTopCoefficientCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5PathMessagePhysicalTransferCoefficient
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramExcitationDecay
import Mathlib.Tactic

/-!
# Vacuum-pair coefficients factor through normalized positive-half transfer

The post-H1-D5 replacement route only needs local matrix coefficients of the
actual canonical-sign finite OS vacuum pair.  The existing literal Wilson path
theorems already identify those coefficients with the complete positive-half
physical transfer, up to the common finite partition normalization.

This file removes that normalization by dividing against the same coefficient
evaluated on the normalized physical top mode at both endpoints.

For every physical endpoint pair x,y,

  <v_OS, x tensor y>
    = gamma * <S_half x, y>,

where
- v_OS is the canonical-sign finite OS vacuum pair,
- gamma = <v_OS, omega_top tensor omega_top>,
- S_half is the normalized H+1-slab physical positive-half transfer.

Thus the partition function disappears completely from the local comparison.
No completed H1-D5 compatibility, no vacuum/top alignment, and no continuum
dynamics is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance vacuumPairRatioTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumPairRatioCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumPairRatioSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumPairRatioMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumPairRatioBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumPairRatioSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance vacuumPairRatioSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section VacuumPairRatio

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

/-- The normalized positive-half transfer fixes the selected normalized
one-slice top mode. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_top_fixed
    (H : ℕ)
    (b : ℝ)
    (hb : 0 ≤ b) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
        H N hN b hb
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN b hb) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN b hb := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN b hb
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN b hb
  have hfix : T omega = omega := by
    simpa [T, omega] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
        H N hN b hb
  change (T ^ periodicHypercubicEvenPositiveHalfCylinderSlabCount H) omega = omega
  induction periodicHypercubicEvenPositiveHalfCylinderSlabCount H with
  | zero =>
      simp
  | succ m ih =>
      rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        hfix, ih]

/-- The canonical-sign finite OS vacuum pair coefficient of any physical
decomposable endpoint pair equals its vacuum/top overlap times the normalized
positive-half physical transfer coefficient.

This is the exact normalization-free finite Wilson identity needed by the
post-#5074 local-top route. -/
theorem
    physicalYangMillsVacuumNormalizedSUNOSVacuumPair_inner_physicalPairDecomposable_eq_vacuumTopOverlap_mul_normalizedPositiveHalf
    (n : ℕ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N) :
    inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          (halfExtent n) N x y) =
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) N hN (beta n) (hbeta n)) *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) x)
          y := by
  let H := halfExtent n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN (beta n) (hbeta n)
  let topPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      H N hN (beta n) (hbeta n)
  let physHalf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
      H N hN (beta n) (hbeta n)
  let normHalf :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
      H N hN (beta n) (hbeta n)
  let c :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN (beta n) (hbeta n)‖⁻¹ ^
      periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  let z :=
    (Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN
          (beta n) (hbeta n)).base.partitionFunction)⁻¹
  let phi :=
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
      H N hN (beta n) (hbeta n)
  have hvacRep :
      (fun q => vac q) =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        phi := by
    simpa [vac, phi, H] using
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_coeFn_eq_boundaryVacuumMomentPairCoordinate
        Q hInvariant n
  have hVacCoeff :
      ∀ a b :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N,
        inner ℝ vac
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
              H N a b) =
          z * inner ℝ (physHalf a) b := by
    intro a b
    have hInner :=
      periodicHypercubicEvenSpecialUnitary_inner_physicalPairDecomposable_eq_literalPairIntegral_of_representative
        H N vac a b phi hvacRep
    have hPath :=
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_pairCoefficient_eq_invSqrtPartition_mul_physicalPositiveHalfTransfer
        H N hN (beta n) (hbeta n) a b
    calc
      inner ℝ vac
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N a b) =
        periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N phi a b := by
            simpa [
              periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
            ] using hInner
      _ = z * inner ℝ (physHalf a) b := by
            simpa [z, physHalf] using hPath
  have hVacXY :
      inner ℝ vac
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N x y) =
        z * inner ℝ (physHalf x) y :=
    hVacCoeff x y
  have hVacTop :
      inner ℝ vac topPair =
        z * inner ℝ (physHalf omega) omega := by
    have hTopDecomp :
        topPair =
          periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N omega omega := by
      rfl
    rw [hTopDecomp]
    exact hVacCoeff omega omega
  have hNormXY :
      inner ℝ (normHalf x) y =
        c * inner ℝ (physHalf x) y := by
    rw [
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_apply_eq_invNormPow_smul_physical
    ]
    rw [real_inner_smul_left]
    rfl
  have hNormTop :
      inner ℝ (normHalf omega) omega = 1 := by
    rw [
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_top_fixed
        H (beta n) (hbeta n)
    ]
    rw [real_inner_self_eq_norm_sq,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm]
    norm_num
  have hTopScale :
      c * inner ℝ (physHalf omega) omega = 1 := by
    rw [hNormXY (x := omega) (y := omega)] at hNormTop
    exact hNormTop
  change
    inner ℝ vac
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N x y) =
      inner ℝ vac topPair * inner ℝ (normHalf x) y
  rw [hVacXY, hVacTop, hNormXY]
  calc
    z * inner ℝ (physHalf x) y =
        z * (c * inner ℝ (physHalf omega) omega) *
          inner ℝ (physHalf x) y := by
      rw [hTopScale]
      ring
    _ =
        (z * inner ℝ (physHalf omega) omega) *
          (c * inner ℝ (physHalf x) y) := by
      ring

end VacuumPairRatio

end

end MathlibAnalytic
end MGAP4D
