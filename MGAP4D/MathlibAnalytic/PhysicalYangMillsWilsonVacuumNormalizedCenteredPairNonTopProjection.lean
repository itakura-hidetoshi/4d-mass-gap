import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedCenteredPairScalarReplacement
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierCompletedOrthogonalDecomposition
import Mathlib.Tactic

/-!
# Canonical physical non-top projection of the actual vacuum-normalized centered pair

After #5064, the finite OS vacuum pair cannot be identified with the physical
pair-top line at positive SU(2) coupling.  Therefore the actual OS-vacuum
centered pair need not itself lie in the physical non-top sector.

The correct unconditional finite-volume receiver is its canonical orthogonal
projection away from the completed physical top-top block.

This file defines that projection for the actual vacuum-normalized centered
two-mode pair and proves:

* the original centered pair is physical by #5063;
* its orthogonal projection lies in the completed physical non-top block;
* the original centered pair decomposes exactly into physical top-top plus
  physical non-top components;
* the non-top projected component receives the already-proved uniform q0^m
  decay with no H1-D5 compatibility, no vacuum/top alignment, and no scalar
  orthogonality assumption.

The remaining model-facing question is no longer membership.  It is whether
these projected excitations are nonzero and scale-coherent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance centeredPairProjectionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance centeredPairProjectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance centeredPairProjectionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance centeredPairProjectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance centeredPairProjectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance centeredPairProjectionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance centeredPairProjectionSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section VacuumNormalizedCenteredPairProjection

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

/-- Physical top-top component of the actual vacuum-normalized centered
two-mode boundary pair. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairTopProjection
    (k : Fin 2) (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
      (halfExtent n) N hN (beta n) (hbeta n)).starProjection
    (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n)

/-- Canonical physical non-top component of the actual vacuum-normalized
centered two-mode boundary pair. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
    (k : Fin 2) (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
      (halfExtent n) N hN (beta n) (hbeta n))ᗮ).starProjection
    (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n)

/-- The actual vacuum-normalized centered pair splits exactly into its physical
top-top and physical non-top orthogonal projections. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPair_top_add_nonTopProjection
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairTopProjection
        Q hInvariant k n +
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        Q hInvariant k n =
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n := by
  let TT :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
      (halfExtent n) N hN (beta n) (hbeta n)
  let x :=
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n
  change TT.starProjection x + (TTᗮ).starProjection x = x
  calc
    TT.starProjection x + (TTᗮ).starProjection x =
        TT.starProjection x + (x - TT.starProjection x) := by
          rw [Submodule.starProjection_orthogonal_val (K := TT)]
    _ = x := by abel

/-- The projected excitation belongs to the completed physical non-top block
without any scalar compatibility assumption. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_mem_nonTop
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        Q hInvariant k n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n) := by
  let x :=
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n
  have hx :
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
    simpa [x] using
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairPhysicalCarrier
        Q hInvariant k n)
  simpa [x,
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_mem_nonTop
      (halfExtent n) N hN (beta n) (hbeta n) x hx

/-- The projected excitation is orthogonal to the entire completed physical
top-top block by construction. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_mem_topTopOrthogonal
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        Q hInvariant k n ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n))ᗮ := by
  exact
    Submodule.starProjection_apply_mem
      ((periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n))ᗮ)
      (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n)

/-- The canonical projected excitation receives uniform q0^m decay
unconditionally on the pair side.

No H1-D5 compatibility, no vacuum/top alignment, and no residual scalar
orthogonality assumption occurs. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_pow_norm_le_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (k : Fin 2) (n m : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ^ m)
        (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
          Q hInvariant k n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
        ‖physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
          Q hInvariant k n‖ := by
  exact
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
      halfExtent N hN beta hbeta s hs hcut n m
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        Q hInvariant k n)
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_mem_nonTop
        Q hInvariant k n)

/-- Under the optional excitation-level scalar compatibility of #5063, the
canonical non-top projection is the original centered vector itself. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_eq_self_of_excitationTopScalarCompatibility
    (hScalar :
      PhysicalYangMillsVacuumNormalizedSUNTwoModeExcitationTopScalarCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        Q hInvariant)
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        Q hInvariant k n =
      physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n := by
  have hOrth :
      physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n))ᗮ := by
    have hAll :
        PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) :=
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredPairTopTopOrthogonal_iff_excitationTopScalarCompatibility
        Q hInvariant).2 hScalar
    exact hAll k n
  unfold
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
  exact
    (Submodule.starProjection_eq_self_iff
      (K :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
          (halfExtent n) N hN (beta n) (hbeta n))ᗮ)).2 hOrth

end VacuumNormalizedCenteredPairProjection

end

end MathlibAnalytic
end MGAP4D
