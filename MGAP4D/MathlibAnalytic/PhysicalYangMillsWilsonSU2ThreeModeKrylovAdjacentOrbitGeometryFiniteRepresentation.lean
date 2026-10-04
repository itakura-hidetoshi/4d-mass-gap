import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometryProjectionSplit
import Mathlib.Tactic

/-!
# Finite-carrier representation of the SU(2) orbit geometry split

PR #5117 splits the remaining orbit-wise cross-volume geometry residual into

* a coarse-reconstruction transfer/refinement commutation residual;
* a fine-side leakage residual outside the coarse embedded range.

This file removes the remaining common-marginal operator opacity.

First, the actual fine-side Krylov orbit is represented exactly as the image of
one finite pair-Haar vector under the fine pair embedding.  Applying the
fine-volume transfer at the frozen coarse coupling stays exactly in that fine
embedded range.

Second, the refinement-commutation residual is pulled back through the coarse
embedding's canonical projected inverse.  Because the coarse embedding is an
isometry, its norm is exactly a norm on the finite coarse pair-Haar carrier.

Thus the two geometry quantities become:

1. a finite coarse-carrier transfer/reconstruction mismatch;
2. the distance of one explicit fine embedded finite vector from the coarse
   embedded range.

No whole-space cross-volume operator compatibility is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentFiniteGeometryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance su2AdjacentFiniteGeometryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance su2AdjacentFiniteGeometrySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance su2AdjacentFiniteGeometryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance su2AdjacentFiniteGeometryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance su2AdjacentFiniteGeometrySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentFiniteGeometrySpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentFiniteGeometryNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance su2AdjacentFiniteGeometryPhysicalPairCarrierComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

/-- Invariance of the physical pair carrier propagates through every natural
power of the normalized physical pair transfer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_mem
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hx :
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N) :
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta ^ m) x ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      H N hN beta hbeta
  let PP := periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N
  change (T ^ m) x ∈ PP
  induction m generalizing x with
  | zero =>
      simpa using hx
  | succ m ih =>
      change (T ^ m) (T x) ∈ PP
      apply ih
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
          H N hN beta hbeta hx

section FiniteOrbitGeometry

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
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Actual finite fine pair-Haar vector underlying the r-th right Krylov orbit. -/
noncomputable def physicalYangMillsSU2AdjacentFinePairOrbitVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent (n + 1)) 2 :=
  (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)) ^ r)
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
      (halfExtent (n + 1)) k)

theorem physicalYangMillsSU2AdjacentFinePairOrbitVector_mem_physicalPairCarrier
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent (n + 1)) 2 := by
  unfold physicalYangMillsSU2AdjacentFinePairOrbitVector
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_pow_mem
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)) r
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent (n + 1)) k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_mem_physicalPairCarrier
        (halfExtent (n + 1)) k)

/-- The common-marginal right orbit is exactly the fine pair embedding of the
finite pair-Haar orbit vector. -/
theorem physicalYangMillsSU2AdjacentCommonRightOrbitVector_eq_finePairEmbedding
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k =
      physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
        (physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) := by
  unfold physicalYangMillsSU2AdjacentCommonRightOrbitVector
  unfold physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode
  unfold physicalYangMillsSU2AdjacentFinePairOrbitVector
  exact
    physicalYangMillsSU2AdjacentCommonRightTransfer_pow_apply_embedding
      Q R n r
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent (n + 1)) k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_mem_physicalPairCarrier
        (halfExtent (n + 1)) k)

/-- Fine finite orbit vector after one additional fine-volume transfer at the
frozen coarse coupling beta n. -/
noncomputable def physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent (n + 1)) 2 :=
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

theorem
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector_mem_physicalPairCarrier
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent (n + 1)) 2 := by
  unfold physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitVector_mem_physicalPairCarrier
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- Applying the frozen-coupling fine common transfer to the actual right orbit
stays exactly in the fine embedded finite pair-Haar range. -/
theorem
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_apply_rightOrbitVector
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
        Q R n (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k) =
      physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
        (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) := by
  rw [physicalYangMillsSU2AdjacentCommonRightOrbitVector_eq_finePairEmbedding
    Q R n r k]
  unfold physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
  simpa [physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector] using
    realLinearIsometrySubspaceProjectedCompression_apply_map_mem
      (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent (n + 1)) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      (physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
      (physicalYangMillsSU2AdjacentFinePairOrbitVector_mem_physicalPairCarrier
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- Explicit distance of the frozen-coupling fine finite vector from the coarse
pair-embedding range in the adjacent common marginal. -/
noncomputable def
    physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let y :=
    physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
      (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
  ‖physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection Q R n y - y‖

/-- The #5117 fine-range leakage residual is exactly the coarse-range distance
of the explicit frozen-coupling fine finite vector. -/
theorem
    physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual_eq_finePairFrozenStepCoarseRangeDistance
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
        Q R n r k =
      physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance
        Q R n r k := by
  unfold
    physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
    physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance
  simp only
  rw [
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_apply_rightOrbitVector
      Q R n r k]

/-- Canonical coarse pair-Haar reconstruction of the actual fine-side orbit
through the projected inverse of the coarse embedding. -/
noncomputable def physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) 2 :=
  realLinearIsometryProjectedInverse
    (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
    (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k)

/-- Physical-carrier projection of the coarse reconstructed orbit vector. -/
noncomputable def physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) 2 :=
  realHilbertSubspaceProjection
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2)
    (physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector Q R n r k)

/-- Coarse projected-inverse reconstruction of the frozen-coupling fine output. -/
noncomputable def
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) 2 :=
  realLinearIsometryProjectedInverse
    (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
    (physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
      Q R n (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k))

/-- Finite coarse-carrier form of the refinement/transfer commutation mismatch. -/
noncomputable def
    physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector
          Q R n r k) -
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector
      Q R n r k‖

theorem physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
        Q R n r k := by
  unfold physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
  exact norm_nonneg _

/-- The #5117 refinement-commutation residual is exactly the finite coarse
pair-Haar norm obtained by projected-inverse reconstruction. -/
theorem
    physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual_eq_finite
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
        Q R n r k =
      physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
        Q R n r k := by
  let J := physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  let z := physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k
  let B :=
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
      Q R n (beta n) (hbeta n)
  unfold
    physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
    physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
    physicalYangMillsSU2AdjacentCoarsePhysicalExtractedOrbitVector
    physicalYangMillsSU2AdjacentCoarseExtractedOrbitVector
    physicalYangMillsSU2AdjacentCoarseExtractedFineFrozenStepVector
    physicalYangMillsSU2AdjacentCommonLeftTransfer
    physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection
    realLinearIsometrySubspaceProjectedCompression
    realLinearIsometryProjectedCompression
  change
    ‖J (T (realHilbertSubspaceProjection M
          (realLinearIsometryProjectedInverse J z))) -
        J (realLinearIsometryProjectedInverse J (B z))‖ =
      ‖T (realHilbertSubspaceProjection M
          (realLinearIsometryProjectedInverse J z)) -
        realLinearIsometryProjectedInverse J (B z)‖
  rw [← J.map_sub, J.norm_map]

/-- Final explicit finite/projective geometry input: a summable finite
coarse-carrier commutation residual, a summable fine-vector coarse-range
distance, and the already explicit weighted beta increments. -/
structure PhysicalYangMillsSU2AdjacentFiniteGeometryBetaSummableInput where
  finiteRefinementCommutation_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFiniteRefinementCommutationResidual
            Q R n r k)
  fineCoarseRangeDistance_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentFinePairFrozenStepCoarseRangeDistance
            Q R n r k)
  betaMajorant_summable :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n)

namespace PhysicalYangMillsSU2AdjacentFiniteGeometryBetaSummableInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentFiniteGeometryBetaSummableInput
        (Q := Q) (R := R))

include G

/-- The finite/projective geometry input theorem-generates the #5117
projection-split closure package. -/
noncomputable def toProjectionBetaSummableInput :
    PhysicalYangMillsSU2AdjacentOrbitProjectionBetaSummableInput
      (Q := Q) (R := R) where
  refinementCommutation_summable := fun r k => by
    simpa only [
      physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual_eq_finite
        Q R] using
      G.finiteRefinementCommutation_summable r k
  fineRangeLeakage_summable := fun r k => by
    simpa only [
      physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual_eq_finePairFrozenStepCoarseRangeDistance
        Q R] using
      G.fineCoarseRangeDistance_summable r k
  betaMajorant_summable := G.betaMajorant_summable

/-- Therefore the finite/projective geometry input already implies every fixed
Krylov-orbit mismatch is summable. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentOrbitProjectionBetaSummableInput.orbitMismatch_summable
      Q R (toProjectionBetaSummableInput Q R G) r k

end PhysicalYangMillsSU2AdjacentFiniteGeometryBetaSummableInput

end FiniteOrbitGeometry

end

end MathlibAnalytic
end MGAP4D
