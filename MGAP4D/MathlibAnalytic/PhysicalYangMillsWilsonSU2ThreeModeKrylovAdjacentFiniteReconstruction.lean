import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometryFiniteRepresentation
import Mathlib.Tactic

/-!
# Canonical finite reconstruction across adjacent SU(2) volumes

PR #5118 represents the remaining H1-C3 orbit geometry by finite pair-Haar
vectors together with the projected inverse of the coarse embedding.

This file packages that projected inverse as one canonical finite reconstruction

  R_n : FinePair(n+1) -> CoarsePair(n).

Its physical version is

  R_n^phys = P_phys,n ∘ R_n.

The finite refinement-commutation residual then splits into

  ||T_n R_n^phys x - R_n^phys y||
    + ||R_n^phys y - R_n y||,

where x is the actual fine Krylov-orbit vector and y is its one-step
fine-volume evolution at the frozen coarse coupling.

Thus the first term is an entirely finite transfer/reconstruction commutator,
while the second measures failure of the reconstructed fine output to lie in
the coarse physical pair carrier.

The other #5118 geometry term is rewritten as the embedding reconstruction
defect

  ||J_n^L (R_n y) - J_n^R y||.

No whole-space cross-volume transfer compatibility is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentFiniteReconstructionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance su2AdjacentFiniteReconstructionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance su2AdjacentFiniteReconstructionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance su2AdjacentFiniteReconstructionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance su2AdjacentFiniteReconstructionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance su2AdjacentFiniteReconstructionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentFiniteReconstructionSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentFiniteReconstructionNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance su2AdjacentFiniteReconstructionPhysicalPairCarrierComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

section AdjacentFiniteReconstruction

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)

/-- Canonical finite reconstruction from the fine pair-Haar carrier to the
coarse pair-Haar carrier through the adjacent common marginal. -/
noncomputable def physicalYangMillsSU2AdjacentFiniteCoarseReconstruction
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2 :=
  (realLinearIsometryProjectedInverse
      (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)).comp
    (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n).toContinuousLinearMap

/-- Physical coarse reconstruction: first reconstruct in the coarse pair-Haar
carrier, then project to its completed physical pair carrier. -/
noncomputable def physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2 :=
  (realHilbertSubspaceProjection
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2)).comp
    (physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n)

/-- The #5118 extracted fine orbit is exactly the canonical finite
reconstruction applied to the actual fine pair-Haar orbit vector. -/
theorem physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector_eq_reconstruction
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector Q R n r k =
      physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
        (physicalYangMillsSU2AdjacentFinePairOrbitVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  unfold
    physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction
  rw [physicalYangMillsSU2AdjacentCommonRightOrbitVector_eq_finePairEmbedding
    Q R n r k]
  rfl

/-- The #5118 physical extracted orbit is exactly physical reconstruction of the
finite fine orbit vector. -/
theorem
    physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector_eq_physicalReconstruction
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector
        Q R n r k =
      physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
        (physicalYangMillsSU2AdjacentFinePairOrbitVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  unfold
    physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction
  rw [
    physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector_eq_reconstruction
      Q R n r k]
  rfl

/-- The #5118 extracted frozen-coupling fine output is exactly the canonical
finite reconstruction of the explicit finite fine output. -/
theorem
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector_eq_reconstruction
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector
        Q R n r k =
      physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
        (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  unfold
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction
  rw [
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_apply_rightOrbitVector
      Q R n r k]
  rfl

/-- Entirely finite transfer/reconstruction commutation defect.  Both terms live
on the coarse pair-Haar carrier. -/
noncomputable def
    physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let x :=
    physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) (Rphys x) -
    Rphys y‖

theorem
    physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
        Q R n r k := by
  unfold
    physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
  exact norm_nonneg _

/-- Coarse physical-carrier leakage of the reconstructed frozen-coupling fine
output. -/
noncomputable def
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  ‖Rphys y - Rcoarse y‖

theorem
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
        Q R n r k := by
  unfold physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
  exact norm_nonneg _

/-- The #5118 finite refinement residual splits into a purely finite physical
transfer/reconstruction commutator plus coarse physical-carrier leakage. -/
theorem
    physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual_le_physicalCommutation_add_coarsePhysicalLeakage
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
        Q R n r k ≤
      physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
          Q R n r k +
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
          Q R n r k := by
  let x :=
    physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  have hsplit :
      T (Rphys x) - Rcoarse y =
        (T (Rphys x) - Rphys y) + (Rphys y - Rcoarse y) := by
    abel
  unfold physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
  rw [
    physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector_eq_physicalReconstruction
      Q R n r k,
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector_eq_reconstruction
      Q R n r k]
  change ‖T (Rphys x) - Rcoarse y‖ ≤ _
  rw [hsplit]
  calc
    ‖(T (Rphys x) - Rphys y) + (Rphys y - Rcoarse y)‖ ≤
      ‖T (Rphys x) - Rphys y‖ + ‖Rphys y - Rcoarse y‖ :=
        norm_add_le _ _
    _ =
      physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
          Q R n r k +
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
          Q R n r k := by
      unfold
        physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
      rfl

/-- Summability of the two finite reconstruction pieces implies summability of
the #5118 finite refinement-commutation residual. -/
theorem
    physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual_summable_of_reconstructionSplit
    (r : ℕ) (k : Fin 3)
    (hCommutation :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
            Q R n r k))
    (hPhysicalLeakage :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
            Q R n r k)) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
          Q R n r k) := by
  have hmajorant :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
              Q R n r k +
            physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
              Q R n r k) :=
    hCommutation.add hPhysicalLeakage
  refine Summable.of_nonneg_of_le
    (fun n =>
      physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual_nonneg
        Q R n r k)
    (fun n =>
      physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual_le_physicalCommutation_add_coarsePhysicalLeakage
        Q R n r k)
    hmajorant

/-- Finite reconstruction defect of a frozen-coupling fine output: reconstruct
it in the coarse finite carrier and re-embed, then compare with the original
fine embedding in the adjacent common marginal. -/
noncomputable def
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  ‖physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n (Rcoarse y) -
    physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n y‖

theorem physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
        Q R n r k := by
  unfold physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
  exact norm_nonneg _

/-- The #5118 coarse-range distance is exactly the canonical finite
reconstruction range residual. -/
theorem
    physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance_eq_finiteReconstructionRangeResidual
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance
        Q R n r k =
      physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
        Q R n r k := by
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Jleft := physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
  let Jright := physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  unfold
    physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
    physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction
    realLinearIsometryProjectedCompression
  change
    ‖Jleft
          (realLinearIsometryProjectedInverse Jleft (Jright y)) -
        Jright y‖ =
      ‖Jleft (Rcoarse y) - Jright y‖
  rfl

/-- Final finite-reconstruction H1-C3 input: all remaining geometry is expressed
through the canonical fine-to-coarse finite reconstruction map, together with
the explicit weighted beta increments. -/
structure PhysicalYangMillsSU2AdjacentFiniteReconstructionBetaSummableInput where
  physicalCommutation_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
            Q R n r k)
  coarsePhysicalLeakage_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
            Q R n r k)
  reconstructionRange_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
            Q R n r k)
  betaMajorant_summable :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n)

namespace PhysicalYangMillsSU2AdjacentFiniteReconstructionBetaSummableInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentFiniteReconstructionBetaSummableInput
        (Q := Q) (R := R))

include G

/-- Convert the finite reconstruction input into the exact #5118 finite
geometry package. -/
noncomputable def toFiniteGeometryBetaSummableInput :
    PhysicalYangMillsSU2AdjacentFiniteGeometryBetaSummableInput
      (Q := Q) (R := R) where
  finiteRefinementCommutation_summable := fun r k =>
    physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual_summable_of_reconstructionSplit
      Q R r k
      (G.physicalCommutation_summable r k)
      (G.coarsePhysicalLeakage_summable r k)
  fineCoarseRangeDistance_summable := fun r k => by
    simpa only [
      physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance_eq_finiteReconstructionRangeResidual
        Q R] using
      G.reconstructionRange_summable r k
  betaMajorant_summable := G.betaMajorant_summable

/-- Hence finite reconstruction summability implies every fixed Krylov-orbit
mismatch is summable. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentFiniteGeometryBetaSummableInput.orbitMismatch_summable
      Q R (toFiniteGeometryBetaSummableInput Q R G) r k

end PhysicalYangMillsSU2AdjacentFiniteReconstructionBetaSummableInput

end AdjacentFiniteReconstruction

end

end MathlibAnalytic
end MGAP4D
