import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSPairTopTopScalarCriterion
import Mathlib.Tactic

/-!
# Vacuum-pair alignment bridge for the concrete SU(N) two-mode centered vectors

The full-pair q0 route of #5009 left two concrete residuals:

1. centered pair membership in the completed physical pair carrier;
2. centered pair orthogonality to the completed pair top-top block.

Top-eigenspace simplicity and #5013 reduce the second residual to one scalar
pair-vacuum coefficient.

This file isolates the exact remaining geometry.  Write E for the exact
boundary-Haar to ordered spatial-slice-pair isometry and J for the finite OS
boundary-moment isometry.  The explicit centered pair vector is exactly

  finiteVacuumCentered (E (J Omega_OS)) (E f_k).

Thus it is automatically orthogonal to the pair-coordinate OS vacuum.  If that
vacuum lies on the selected physical pair-top line, #5013 converts this into
the full top-top orthogonality residual.  The same alignment places the vacuum
term in the physical pair carrier, so centered carrier membership follows once
the uncentered primary-plaquette pair vector is known to be physical.

No one-sided factorization, pairWeakAtFor input, or top-eigenspace simplicity
assumption remains: simplicity is now a theorem from #5012.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance sunTwoModeVacuumPairAlignmentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeVacuumPairAlignmentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeVacuumPairAlignmentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeVacuumPairAlignmentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeVacuumPairAlignmentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Vacuum centering is orthogonal to a normalized vacuum in any real inner
product space. -/
theorem inner_finiteVacuumCentered_eq_zero_of_norm_one
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (vacuum x : E)
    (hvacuum : ‖vacuum‖ = 1) :
    inner ℝ vacuum (finiteVacuumCentered vacuum x) = 0 := by
  unfold finiteVacuumCentered
  rw [inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hvacuum]
  ring

section SUNTwoModeVacuumPairAlignment

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

/-- Pair-coordinate image of the normalized finite OS vacuum. -/
noncomputable def physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
    (halfExtent n) N (J Pn.vacuum)

/-- Pair-coordinate image of the explicit uncentered primary-plaquette
two-mode boundary vector. -/
noncomputable def physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
    (k : Fin 2) (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
    (halfExtent n) N
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
      (halfExtent n) hN2 k)

/-- Exact pair-coordinate form of the #5008/#5009 centered vector. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) k n =
      finiteVacuumCentered
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) n)
        (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
          (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let E :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N
  change
    E
        (finiteVacuumCentered
          (J Pn.vacuum)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
            (halfExtent n) hN2 k)) =
      finiteVacuumCentered
        (E (J Pn.vacuum))
        (E
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
            (halfExtent n) hN2 k))
  exact linearIsometry_finiteVacuumCentered E (J Pn.vacuum)
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
      (halfExtent n) hN2 k)

/-- The pair-coordinate finite OS vacuum has norm one. -/
theorem physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_norm
    (n : ℕ) :
    ‖physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n‖ = 1 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let E :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change ‖E (J Pn.vacuum)‖ = 1
  calc
    ‖E (J Pn.vacuum)‖ = ‖J Pn.vacuum‖ := E.norm_map _
    _ = ‖Pn.vacuum‖ := J.norm_map _
    _ = 1 := Pn.norm_vacuum hPn

/-- Structural vacuum condition left after #5012/#5013: at every cutoff, the
finite OS vacuum in ordered endpoint-pair coordinates lies on the selected
physical pair-top line. -/
def PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment : Prop :=
  ∀ n : ℕ,
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n ∈
      ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
        (halfExtent n) N hN (beta n) (hbeta n)

/-- The only non-vacuum carrier condition left by the full-pair route:
the uncentered explicit primary-plaquette pair vector is physical. -/
def PhysicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier : Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
        (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N

/-- The selected pair-top vector itself belongs to the completed physical pair
carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_mem_physicalPairCarrier
    (H N : ℕ) (hN : 0 < N) (b : ℝ) (hb : 0 ≤ b) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
        H N hN b hb ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  have hSpan :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN b hb ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
          H N hN b hb := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_eq_span_pairTopMode
        H N hN b hb]
    exact
      Submodule.mem_span_singleton_self
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN b hb)
  have hClosure :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN b hb ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
          H N hN b hb := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
        H N hN b hb).le_topologicalClosure hSpan
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_le_physicalPairCarrier
      H N hN b hb hClosure

/-- Vacuum-pair alignment theorem-generates the scalar top-pair orthogonality
condition for every explicit centered two-mode vector. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal_of_vacuumPairTopAlignment
    (hAlign :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant)) :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  intro k n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q) (hInvariant := hInvariant) n
  let top :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      (halfExtent n) N hN (beta n) (hbeta n)
  let x :=
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n
  have hvacNorm : ‖vac‖ = 1 := by
    simpa [vac] using
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_norm
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) n
  have hCentered :
      physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n =
        finiteVacuumCentered vac x := by
    simpa [vac, x] using
      physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) k n
  have hVacOrth :
      inner ℝ vac
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n) = 0 := by
    rw [hCentered]
    exact inner_finiteVacuumCentered_eq_zero_of_norm_one vac x hvacNorm
  have hAlignN : vac ∈ ℝ ∙ top := by
    simpa [vac, top] using hAlign n
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hAlignN
  have hcNe : c ≠ 0 := by
    intro hcZero
    have hvacZero : vac = 0 := by
      rw [← hc, hcZero, zero_smul]
    rw [hvacZero, norm_zero] at hvacNorm
    norm_num at hvacNorm
  have hScaled :
      c * inner ℝ top
          (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN) (hN2 := hN2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q) (hInvariant := hInvariant) k n) = 0 := by
    calc
      c * inner ℝ top
          (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN) (hN2 := hN2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q) (hInvariant := hInvariant) k n) =
        inner ℝ (c • top)
          (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN) (hN2 := hN2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q) (hInvariant := hInvariant) k n) :=
          (real_inner_smul_left top
            (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN) (hN2 := hN2)
              (beta := beta) (hbeta := hbeta)
              (Q := Q) (hInvariant := hInvariant) k n) c).symm
      _ = inner ℝ vac
          (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN) (hN2 := hN2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q) (hInvariant := hInvariant) k n) := by rw [hc]
      _ = 0 := hVacOrth
  exact (mul_eq_zero.mp hScaled).resolve_left hcNe

/-- Vacuum-pair alignment and uncentered physicality theorem-generate the
#5009 centered physical-pair-carrier residual. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier_of_vacuumPairTopAlignment_uncentered
    (hAlign :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hUncentered :
      PhysicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier
        (halfExtent := halfExtent) (N := N) (hN2 := hN2)) :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  intro k n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q) (hInvariant := hInvariant) n
  let top :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      (halfExtent n) N hN (beta n) (hbeta n)
  let x :=
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) N
  have hTopP : top ∈ P := by
    simpa [top, P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_mem_physicalPairCarrier
        (halfExtent n) N hN (beta n) (hbeta n)
  have hSpanLe : ℝ ∙ top ≤ P :=
    (Submodule.span_singleton_le_iff_mem top P).2 hTopP
  have hVacP : vac ∈ P := by
    apply hSpanLe
    simpa [vac, top] using hAlign n
  have hXP : x ∈ P := by
    simpa [x, P] using hUncentered k n
  rw [
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q) (hInvariant := hInvariant) k n]
  unfold finiteVacuumCentered
  exact
    Submodule.sub_mem P hXP
      (Submodule.smul_mem P
        (inner ℝ vac x) hVacP)

/-- The two structural inputs above theorem-generate both #5009 residuals. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredFullPairResiduals_of_vacuumPairTopAlignment_uncentered
    (hAlign :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hUncentered :
      PhysicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier
        (halfExtent := halfExtent) (N := N) (hN2 := hN2)) :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) ∧
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  constructor
  · exact
      physicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier_of_vacuumPairTopAlignment_uncentered
        hAlign hUncentered
  · apply
      (physicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal_iff_scalar
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant)).2
    exact
      physicalYangMillsSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal_of_vacuumPairTopAlignment
        hAlign

/-- Direct q0^m consequence under only the structural vacuum alignment and
uncentered physical-carrier statements. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0_of_vacuumPairTopAlignment_uncentered
    (hAlign :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hUncentered :
      PhysicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier
        (halfExtent := halfExtent) (N := N) (hN2 := hN2))
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
  obtain ⟨hCarrier, hOrth⟩ :=
    physicalYangMillsSUNTwoModeExplicitCenteredFullPairResiduals_of_vacuumPairTopAlignment_uncentered
      hAlign hUncentered
  exact
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0
      hCarrier hOrth s hs hcut k n m

end SUNTwoModeVacuumPairAlignment

end

end MathlibAnalytic
end MGAP4D
