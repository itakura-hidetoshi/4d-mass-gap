import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedEquality
import Mathlib.Tactic

/-!
# Vacuum-normalized centered-pair replacement seam after the H1-D5 no-go

The completed H1-D5 transfer compatibility is false at positive SU(2)
coupling. The quantitative q0 route does not need that operator statement.

This file keeps only the excitation-level geometry actually required by the
full-pair non-top estimate.

* H1-D4 (#5029) puts the canonical-sign vacuum-normalized OS vacuum pair in the
  completed physical pair carrier.
* #5015 puts every uncentered primary-plaquette two-mode pair in the same
  physical carrier.
* Hence their finite-vacuum-centered difference is automatically physical,
  without any transfer compatibility or vacuum/top alignment.
* The remaining top-top orthogonality condition is rewritten as one scalar
  equality for the actual excitation.

Thus the replacement seam is a single matrix coefficient per selected mode and
finite scale, rather than equality of two completed transfer operators.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance vacuumNormalizedCenteredPairTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumNormalizedCenteredPairCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumNormalizedCenteredPairSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumNormalizedCenteredPairMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumNormalizedCenteredPairBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumNormalizedCenteredPairSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance vacuumNormalizedCenteredPairSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section VacuumNormalizedCenteredPair

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

/-- The vacuum-normalized centered two-mode pair is in the completed physical
pair carrier with no transfer compatibility and no vacuum/top alignment.

The two terms in finiteVacuumCentered are already physical independently:
the uncentered mode by #5015 and the canonical-sign vacuum pair by H1-D4
closure #5029. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairPhysicalCarrier :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) := by
  intro k n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  let x :=
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) N
  have hvacP : vac ∈ P := by
    simpa [vac, P] using
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_mem_physicalPairCarrier
        Q hInvariant n
  have hxP : x ∈ P := by
    simpa [x, P] using
      (physicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier
        (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n)
  rw [
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n]
  unfold finiteVacuumCentered
  exact
    Submodule.sub_mem P hxP
      (Submodule.smul_mem P (inner ℝ vac x) hvacP)

/-- Exact scalar expansion of the remaining top-pair coefficient of the
vacuum-normalized centered excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopPair_inner_eq
    (k : Fin 2) (n : ℕ) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n))
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n) =
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) N hN (beta n) (hbeta n))
          (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
            (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) -
        inner ℝ
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
            (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
              (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) *
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
              (halfExtent n) N hN (beta n) (hbeta n))
            (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
              (S := S) (D := D) (halfExtent := halfExtent)
              (N := N) (hN := hN)
              (beta := beta) (hbeta := hbeta)
              (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n) := by
  rw [
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n]
  unfold finiteVacuumCentered
  rw [inner_sub_right, real_inner_smul_right]

/-- Excitation-level replacement for the false completed H1-D5 seam.

It asks only that the selected pair-top coefficient of the uncentered
excitation factor through its finite-OS-vacuum coefficient. This is exactly
what is needed for vacuum centering to remove the pair-top component. -/
def
    PhysicalYangMillsVacuumNormalizedSUNTwoModeExcitationTopScalarCompatibility :
    Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n))
        (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
          (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) =
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
            (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n) *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) N hN (beta n) (hbeta n))
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)

/-- The new excitation-level scalar compatibility is exactly the scalar
top-pair orthogonality residual of #5013 for the vacuum-normalized centered
vectors. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal_iff_excitationTopScalarCompatibility :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) ↔
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExcitationTopScalarCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        Q hInvariant := by
  constructor
  · intro h k n
    have hz := h k n
    rw [
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopPair_inner_eq
        Q hInvariant k n] at hz
    exact sub_eq_zero.mp hz
  · intro h k n
    rw [
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopPair_inner_eq
        Q hInvariant k n]
    exact sub_eq_zero.mpr (h k n)

/-- After #5012/#5013, the new excitation-level scalar condition is exactly
the completed pair top-top orthogonality condition. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopTopOrthogonal_iff_excitationTopScalarCompatibility :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) ↔
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExcitationTopScalarCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        Q hInvariant := by
  rw [physicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal_iff_scalar]
  exact
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal_iff_excitationTopScalarCompatibility
      Q hInvariant

/-- With physical-carrier membership now theorem-generated, the replacement
scalar condition is the only finite pair-side input needed to place every
vacuum-normalized centered two-mode vector in the full completed non-top
sector. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairL2_mem_nonTop_of_excitationTopScalarCompatibility
    (hScalar :
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExcitationTopScalarCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        Q hInvariant)
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n) := by
  apply
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_mem_nonTop
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairPhysicalCarrier
        Q hInvariant)
  exact
    (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopTopOrthogonal_iff_excitationTopScalarCompatibility
      Q hInvariant).2 hScalar k n

/-- Direct q0^m estimate under the excitation-level scalar replacement seam.

No completed OS/physical transfer compatibility and no vacuum/top line
alignment appears in the assumptions. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0_of_excitationTopScalarCompatibility
    (hScalar :
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExcitationTopScalarCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        Q hInvariant)
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
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
        ‖physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n‖ := by
  exact
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
      halfExtent N hN beta hbeta s hs hcut n m
      (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n)
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairL2_mem_nonTop_of_excitationTopScalarCompatibility
        Q hInvariant hScalar k n)

end VacuumNormalizedCenteredPair

end

end MathlibAnalytic
end MGAP4D
