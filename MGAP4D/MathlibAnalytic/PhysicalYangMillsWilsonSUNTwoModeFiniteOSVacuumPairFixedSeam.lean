import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryTransferSpatialSlicePair
import Mathlib.Tactic

/-!
# Vacuum-pair fixed-space seam for the concrete SU(N) two-mode route

After #5015, the only remaining H1-D structural input is finite OS vacuum-pair
alignment with the selected physical pair-top line.

This file rewrites that alignment in operator language.

First, one-slice top-eigenspace simplicity and the scalar top-top criterion are
upgraded to an exact pair statement: the completed pair top-top block itself is
the one-dimensional span of the selected pair top mode.

Second, the finite OS vacuum pair is shown to be fixed automatically by the
completed OS boundary transfer after exact transport to ordered endpoint-pair
coordinates.

Therefore vacuum alignment follows from two concrete model-facing facts only:

1. the finite OS vacuum pair belongs to the completed physical pair carrier;
2. on that single vacuum vector, the normalized physical pair transfer agrees
   with the pair-coordinate completed OS boundary transfer.

No all-input operator intertwining is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance sunTwoModeVacuumPairFixedSeamTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeVacuumPairFixedSeamCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeVacuumPairFixedSeamSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeVacuumPairFixedSeamMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeVacuumPairFixedSeamBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sunTwoModeVacuumPairFixedSeamSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance sunTwoModeVacuumPairFixedSeamSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section PairTopLine

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N

local notation "PairTop" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
    H N hN beta hbeta

local notation "TTspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
    H N hN beta hbeta

local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
    H N hN beta hbeta

/-- The completed pair top-top block is exactly the selected one-dimensional
pair-top line. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_eq_span_pairTopMode :
    TT = ℝ ∙ PairTop := by
  have hPairTopSpan : PairTop ∈ TTspan := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_eq_span_pairTopMode
        H N hN beta hbeta]
    exact Submodule.mem_span_singleton_self PairTop
  have hPairTopTT : PairTop ∈ TT := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure]
    exact TTspan.le_topologicalClosure hPairTopSpan
  apply le_antisymm
  · intro x hx
    let c : ℝ := inner ℝ PairTop x
    let y : PairE := x - c • PairTop
    have hyTT : y ∈ TT := by
      exact
        Submodule.sub_mem TT hx
          (Submodule.smul_mem TT c hPairTopTT)
    have hyOrth : y ∈ TTᗮ := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_orthogonal_mem_iff_pairTopMode_inner_eq_zero
          H N hN beta hbeta]
      dsimp [y, c]
      rw [inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_norm]
      ring
    have hyZero : y = 0 := by
      have hinner : inner ℝ y y = 0 := by
        rw [Submodule.mem_orthogonal] at hyOrth
        exact hyOrth y hyTT
      exact inner_self_eq_zero.mp hinner
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    dsimp [y] at hyZero
    exact (sub_eq_zero.mp hyZero).symm
  · exact
      (Submodule.span_singleton_le_iff_mem PairTop TT).2 hPairTopTT

end PairTopLine

section SUNTwoModeVacuumFixedSeam

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Physical-carrier part of the remaining finite OS vacuum-pair seam. -/
def PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairPhysicalCarrier : Prop :=
  ∀ n : ℕ,
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N

/-- Fixed-vector part of the remaining finite OS vacuum-pair seam. -/
def PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairNormalizedTransferFixed : Prop :=
  ∀ n : ℕ,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n) =
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n

/-- Physical-pair membership plus normalized-transfer fixedness theorem-generate
the old vacuum-pair top-line alignment condition. -/
theorem physicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment_of_carrier_fixed
    (hCarrier :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hFixed :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairNormalizedTransferFixed
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant)) :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  intro n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q) (hInvariant := hInvariant) n
  have hTop :
      vac ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
          (halfExtent n) N hN (beta n) (hbeta n) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n) vac
        (by simpa [vac] using hCarrier n)).1
        (by simpa [vac] using hFixed n)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_eq_span_pairTopMode
      (halfExtent n) N hN (beta n) (hbeta n)] at hTop
  simpa [vac] using hTop

/-- The pair-coordinate finite OS vacuum is fixed automatically by every
completed OS boundary transfer. -/
theorem physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_completedBoundaryPairTransfer_fixed
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) :
    periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
        (halfExtent n) N
        (Q.completedBoundaryTransfer hInvariant C n t)
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n) =
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let E :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N
  change
    E
      (Q.completedBoundaryTransfer hInvariant C n t
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          (halfExtent n) N (E (J Pn.vacuum)))) =
      E (J Pn.vacuum)
  rw [periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse]
  rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
  have hVac :=
    C.finiteOperator_fixes_vacuum n (t / 2)
  change C.finiteOperator n (t / 2) Pn.vacuum = Pn.vacuum at hVac
  rw [hVac]

/-- One-vector compatibility between the pair transfer used by #5006 and the
completed OS boundary transfer used by the finite OS Hilbert construction. -/
def PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) : Prop :=
  ∀ n : ℕ,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n) =
      periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
        (halfExtent n) N
        (Q.completedBoundaryTransfer hInvariant C n 2)
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n)

/-- The one-vector completed-transfer compatibility theorem-generates normalized
physical pair-transfer fixedness of the finite OS vacuum pair. -/
theorem physicalYangMillsSUNTwoModeExplicitOSVacuumPairNormalizedTransferFixed_of_completedCompatibility
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) C) :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairNormalizedTransferFixed
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  intro n
  calc
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n) =
      periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
        (halfExtent n) N
        (Q.completedBoundaryTransfer hInvariant C n 2)
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n) := hCompat n
    _ =
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n :=
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_completedBoundaryPairTransfer_fixed
        C n 2

/-- Physical carrier membership plus the one-vector completed-transfer
compatibility theorem-generate the old vacuum alignment condition. -/
theorem physicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment_of_carrier_completedCompatibility
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (hCarrier :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) C) :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  exact
    physicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment_of_carrier_fixed
      hCarrier
      (physicalYangMillsSUNTwoModeExplicitOSVacuumPairNormalizedTransferFixed_of_completedCompatibility
        C hCompat)

/-- Direct q0 power decay from the explicit residual seam: physical carrier
membership of the finite OS vacuum pair and one-vector transfer compatibility. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0_of_vacuumCarrier_completedCompatibility
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (hCarrier :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) C)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (k : Fin 2) (n m : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ^ m)
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
        ‖physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n‖ := by
  apply
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0_of_vacuumAlignment
  · exact
      physicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment_of_carrier_completedCompatibility
        C hCarrier hCompat
  · exact hs
  · exact hcut

end SUNTwoModeVacuumFixedSeam

end

end MathlibAnalytic
end MGAP4D
