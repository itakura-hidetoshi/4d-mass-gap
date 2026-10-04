import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGeometryBetaClosure
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression
import Mathlib.Tactic

/-!
# Split the orbit-wise cross-volume geometry residual by coarse-range projection

After PR #5116 the only non-scalar model-facing H1-C3 quantity is the
orbit-wise frozen-coupling geometry residual

  g_{n,r,k}
    = ||(A_n^L - B_{n,beta_n}^R) z_{n,r,k}||.

Here `A_n^L` is the coarse-volume common-marginal transfer,
`B_{n,beta_n}^R` is the fine-volume common-marginal transfer evaluated at the
same coarse coupling, and `z_{n,r,k}` is the actual fine-side Krylov-orbit
vector.

Let `P_n^L` be the canonical orthogonal projection onto the range of the
coarse pair-Haar embedding in the adjacent common marginal.  Inserting
`P_n^L` after the frozen-coupling fine transfer gives

  g_{n,r,k}
    <= ||A_n^L z - P_n^L (B_n^R z)||
       + ||P_n^L (B_n^R z) - B_n^R z||.

The first term is the orbit-wise transfer/refinement commutation residual after
canonical coarse reconstruction.  The second is the fine-side leakage outside
the coarse embedded range.

This split remains vector-wise: it does not reintroduce whole-space
cross-volume operator compatibility.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentOrbitProjectionSplitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentOrbitProjectionSplitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentOrbitProjectionSplitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentOrbitProjectionSplitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentOrbitProjectionSplitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentOrbitProjectionSplitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentOrbitProjectionSplitSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentOrbitProjectionSplitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section OrbitGeometryProjectionSplit

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

/-- Canonical orthogonal projection onto the coarse pair-Haar embedding range
inside the adjacent common marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection
    (n : ℕ) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  realLinearIsometryProjectedCompression
    (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
    (1 :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent n) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent n) 2)

/-- The coarse-range projection fixes every vector already in the coarse
embedded pair-Haar range. -/
@[simp] theorem physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection_apply_embedding
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection Q R n
        (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n x) =
      physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n x := by
  unfold physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection
  simpa using
    realLinearIsometryProjectedCompression_apply_map
      (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
      (1 :
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
            (halfExtent n) 2 →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
            (halfExtent n) 2)
      x

/-- Orbit-wise mismatch between the coarse transfer and the canonical coarse
reconstruction of the frozen-coupling fine transfer. -/
noncomputable def
    physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let z := physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k
  let B :=
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
      Q R n (beta n) (hbeta n)
  ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n z -
    physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection Q R n (B z)‖

theorem
    physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
        Q R n r k := by
  unfold
    physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
  exact norm_nonneg _

/-- Orbit-wise part of the frozen-coupling fine transfer which remains outside
the coarse embedded pair-Haar range. -/
noncomputable def
    physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let z := physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k
  let B :=
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
      Q R n (beta n) (hbeta n)
  ‖physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection Q R n (B z) -
    B z‖

theorem
    physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
        Q R n r k := by
  unfold
    physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
  exact norm_nonneg _

/-- The remaining orbit-wise cross-volume geometry residual splits into a
coarse-reconstruction commutation term and a fine-range leakage term. -/
theorem
    physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual_le_refinementCommutation_add_fineRangeLeakage
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
        Q R n r k ≤
      physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
          Q R n r k +
        physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
          Q R n r k := by
  let z := physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k
  let A := physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n
  let B :=
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
      Q R n (beta n) (hbeta n)
  let P := physicalYangMillsSU2AdjacentCommonLeftPairRangeProjection Q R n
  have hsplit :
      (A - B) z =
        (A z - P (B z)) + (P (B z) - B z) := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  unfold physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
  change ‖(A - B) z‖ ≤ _
  rw [hsplit]
  calc
    ‖(A z - P (B z)) + (P (B z) - B z)‖ ≤
      ‖A z - P (B z)‖ + ‖P (B z) - B z‖ :=
        norm_add_le _ _
    _ =
      physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
          Q R n r k +
        physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
          Q R n r k := by
      unfold
        physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
        physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
      rfl

/-- Summability of the two projection-split geometry pieces implies
summability of the original #5108 orbit geometry residual. -/
theorem
    physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual_summable_of_projectionSplit
    (r : ℕ) (k : Fin 3)
    (hCommutation :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
            Q R n r k))
    (hLeakage :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
            Q R n r k)) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
          Q R n r k) := by
  have hmajorant :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
              Q R n r k +
            physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
              Q R n r k) :=
    hCommutation.add hLeakage
  refine Summable.of_nonneg_of_le
    (fun n =>
      physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual_nonneg
        Q R n r k)
    (fun n =>
      physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual_le_refinementCommutation_add_fineRangeLeakage
        Q R n r k)
    hmajorant

/-- Final model-facing H1-C3 input after the geometry projection split:
summable refinement commutation, summable fine-range leakage, and the explicit
weighted beta-increment condition. -/
structure PhysicalYangMillsSU2AdjacentOrbitProjectionBetaSummableInput where
  refinementCommutation_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitRefinementCommutationResidual
            Q R n r k)
  fineRangeLeakage_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitFineRangeLeakageResidual
            Q R n r k)
  betaMajorant_summable :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant halfExtent beta n)

namespace PhysicalYangMillsSU2AdjacentOrbitProjectionBetaSummableInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentOrbitProjectionBetaSummableInput
        (Q := Q) (R := R))

include G

/-- Projection-split geometry data theorem-generates the #5116
geometry-plus-explicit-beta package. -/
noncomputable def toGeometryBetaSummableInput :
    PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput
      (Q := Q) (R := R) where
  orbitGeometry_summable := fun r k =>
    physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual_summable_of_projectionSplit
      Q R r k
      (G.refinementCommutation_summable r k)
      (G.fineRangeLeakage_summable r k)
  betaMajorant_summable := G.betaMajorant_summable

/-- Hence the projection-split input gives every fixed Krylov-orbit mismatch
summable without any whole-space cross-volume compatibility. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput.orbitMismatch_summable
      Q R (toGeometryBetaSummableInput Q R G) r k

/-- Produce the exact #5106 orbit-mismatch package from the projection split. -/
noncomputable def toOrbitMismatchSummableInput :
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput
      (Q := Q) (R := R) :=
  PhysicalYangMillsSU2AdjacentOrbitGeometryBetaSummableInput.toOrbitMismatchSummableInput
    Q R (toGeometryBetaSummableInput Q R G)

end PhysicalYangMillsSU2AdjacentOrbitProjectionBetaSummableInput

end OrbitGeometryProjectionSplit

end

end MathlibAnalytic
end MGAP4D
