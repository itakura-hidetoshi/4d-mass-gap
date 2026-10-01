import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSCenteredBoundaryFormula
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairUniformNonTopDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierCompletedOrthogonalDecomposition
import Mathlib.Tactic

/-!
# Full-pair non-top q0 bridge for the concrete SU(N) two-mode centered boundary vectors

PR #5008 rewrites the boundary image of every concrete centered finite OS
two-mode state as an explicit boundary-Haar vector.  This file moves that vector
through the exact shared-boundary/two-spatial-slice coordinate isometry and
uses the completed physical pair decomposition

  NonTop = PhysicalPairCarrier ∩ TopTop^⊥.

Hence one-sided factorization as `x ⊗ Ω_top` is not required for the pair-side
quantitative estimate.  It suffices to prove exactly two concrete statements:

1. the explicit centered endpoint-pair vector belongs to the completed physical
   pair carrier;
2. it is orthogonal to the completed full top-top block.

Under those two statements, the vector lies in the full completed physical
non-top block and therefore inherits the scale-uniform q0^m decay of #5006 for
every discrete power m.

No vacuum-line/top-eigenspace equality and no top-sector simplicity is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance sunTwoModeFullPairBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeFullPairBridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeFullPairBridgeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeFullPairBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeFullPairBridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

section SUNTwoModeFullPairBridge

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

/-- The #5008 explicit centered boundary vector, expressed in the actual
ordered primary/antipodal spatial-slice pair Haar carrier. -/
noncomputable def physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
    (k : Fin 2) (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
    (halfExtent n) N
    (finiteVacuumCentered
      (J Pn.vacuum)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
        (halfExtent n) hN2 k))

/-- First concrete residual for the full-pair route: every explicit centered
two-mode pair vector lies in the completed physical pair carrier. -/
def PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier : Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) k n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N

/-- Second concrete residual for the full-pair route: every explicit centered
two-mode pair vector is orthogonal to the entire completed top-top block. -/
def PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal : Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) k n ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n))ᗮ

/-- The two full-pair residuals theorem-generate membership in the completed
physical non-top block. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_mem_nonTop
    (hCarrier :
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hOrth :
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) k n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopClosure_eq_carrier_inf_topTopOrthogonal
      (halfExtent n) N hN (beta n) (hbeta n)]
  exact ⟨hCarrier k n, hOrth k n⟩

/-- Direct full-pair quantitative consequence: the explicit centered boundary
pair vector has uniform q0^m decay for every discrete power m.

This is stronger on the pair side than the one-step estimate of #5005 and does
not require choosing a one-sided excitation or proving `pairWeakAtFor`. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0
    (hCarrier :
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (hOrth :
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
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
  exact
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
      halfExtent N hN beta hbeta s hs hcut n m
      (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) k n)
      (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_mem_nonTop
        hCarrier hOrth k n)

end SUNTwoModeFullPairBridge

end

end MathlibAnalytic
end MGAP4D
